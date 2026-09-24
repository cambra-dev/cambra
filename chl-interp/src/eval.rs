//! Evaluating a CHL program to what each of its sinks observed.
//!
//! A program's observable is its sinks, not a returned value, so evaluation answers a map
//! from sink name to the collection of contributions that sink received. A trailing bare
//! expression is a test convenience in the compiler; here it is evaluated and observed by
//! nothing.
//!
//! **A feed nests.** The channel a sink reads is indexed by the feed site's iteration
//! domain — unit where the site does not iterate, the loop's key under one loop, and the
//! tuple of the enclosing loops' keys under several — and whatever was fed sits under that
//! key whatever its shape. So `out << [2, 4, 6]` is one contribution holding a
//! three-element collection, and `for x in xs: out << e` is one contribution per iteration
//! under the key `x` was drawn from.
//!
//! **What it refuses to judge.** Where `docs/chl-spec.md` leaves a value undefined
//! (partial arithmetic, "Partiality is not yet defined \[Open\]") or arbitrary (an as-of
//! read, "8.3 Reads"; two `with` blocks writing one variable, whose commits "8.5 Ordering and
//! concurrency" leaves unordered), evaluation answers an [`Error`] rather than picking a
//! value, so a compiler that picks a different one is not reported as wrong. A read of a
//! channel before every feed to it has run is refused for the same reason: the read denotes
//! the whole collection, which evaluation in program order has not built yet.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use chl_parser::ast::{
    AssignTarget, AugOp, BinOp, BoolOp, CmpOp, CompClause, Expr, IfBranch, Lit, PayloadPattern,
    Spanned, Stmt, TypeAnnotation, UnaryOp, VariantPayload,
};

use crate::value::{Collection, Value};

#[derive(Clone, Debug, PartialEq)]
pub struct Error(pub String);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

fn err<T>(msg: impl Into<String>) -> Result<T, Error> {
    Err(Error(msg.into()))
}

/// What each sink observed.
pub type Observations = BTreeMap<String, Value>;

/// A mutable variable's storage.
///
/// Shared by reference: a write inside a loop body lands in the cell its declaration made,
/// which outlives the iteration's scope, and a `Mut` parameter aliases its argument's cell.
struct MutCell {
    value: Value,
    /// Sequenced by `Txn` rather than by an induction extent, which decides where a read
    /// of it is determinate ("8.3 Reads").
    txn: bool,
}

#[derive(Clone)]
enum Slot {
    Val(Value),
    Mut(Rc<RefCell<MutCell>>),
}

type Scope = Vec<(String, Slot)>;

/// A user function: its parameters, its body, and the scopes it captured at its definition,
/// which its body resolves names against.
#[derive(Clone)]
struct Function {
    params: Vec<(String, bool)>,
    body: Vec<Spanned<Stmt>>,
    env: Vec<Scope>,
}

/// A `with begin():` block in progress.
///
/// Whether the block commits is decided by what it did: a block that wrote nothing and
/// replied nothing took no path to a write, which is a denial. `wrote` records that, so no
/// state has real writes and no commit.
struct TxnFrame {
    wrote: bool,
    /// The mutable variables the block writes anywhere in its body. A read of a `Txn`
    /// variable the block does not write is an as-of read.
    writes: BTreeSet<String>,
    /// Replies fed inside the block, held until the block commits and its commit time is known.
    replies: Vec<(String, usize, Value)>,
}

/// An open channel: what `defer()` or `test_sink()` made.
#[derive(Default)]
struct Channel {
    /// Contributions: the feed site that made each, its key, and its value.
    fed: Vec<(usize, Value, Value)>,
    /// The value a `<<=` defined the channel as.
    defined: Option<Value>,
    /// Every feed site naming this channel, in source order.
    ///
    /// A channel fed from more than one place is a union of those places, and its keys are
    /// tagged by which one. The tagging is a property of the program text, so a site that
    /// never fires still counts.
    sites: Vec<usize>,
}

pub(crate) struct Interp {
    /// Lexical scopes, innermost last.
    scopes: Vec<Scope>,
    channels: BTreeMap<String, Channel>,
    /// The channels a `test_sink()` opened, which are what `run` answers with.
    observed: BTreeSet<String>,
    /// Feed sites per channel name, collected from the program text before it runs.
    feed_sites: BTreeMap<String, Vec<usize>>,
    /// The values a generator has yielded, while one is running.
    yielded: Option<Vec<(Value, Value)>>,
    /// The commit times transaction blocks have taken. They are dense and 1-based: a block
    /// that denies takes none, so they count commits rather than blocks.
    commit_time: i64,
    /// The block in progress, while one is.
    txn: Option<TxnFrame>,
    /// For each feed site, the source position where the top-level statement enclosing it
    /// ends: the point past which that site contributes nothing more.
    feed_done_at: BTreeMap<usize, usize>,
    /// Sources the harness supplied, by the name a zero-argument call names.
    sources: BTreeMap<String, Collection>,
    functions: BTreeMap<String, Function>,
    /// The keys of the loops enclosing the current statement, outermost first.
    loop_keys: Vec<Value>,
}

impl Interp {
    fn new(
        sources: BTreeMap<String, Collection>,
        feed_sites: BTreeMap<String, Vec<usize>>,
        feed_done_at: BTreeMap<usize, usize>,
    ) -> Self {
        Self {
            scopes: vec![Vec::new()],
            channels: BTreeMap::new(),
            observed: BTreeSet::new(),
            feed_sites,
            yielded: None,
            commit_time: 0,
            txn: None,
            feed_done_at,
            sources,
            functions: BTreeMap::new(),
            loop_keys: Vec::new(),
        }
    }

    fn slot(&self, name: &str) -> Option<&Slot> {
        self.scopes
            .iter()
            .rev()
            .find_map(|s| s.iter().rev().find(|(n, _)| n == name).map(|(_, v)| v))
    }

    /// The cell `name` resolves to, when its innermost binding is a mutable variable.
    fn mut_cell(&self, name: &str) -> Option<Rc<RefCell<MutCell>>> {
        match self.slot(name)? {
            Slot::Mut(cell) => Some(cell.clone()),
            Slot::Val(_) => None,
        }
    }

    fn bind(&mut self, name: impl Into<String>, slot: Slot) {
        self.scopes
            .last_mut()
            .expect("at least one scope")
            .push((name.into(), slot));
    }

    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(Vec::new());
        let out = f(self);
        self.scopes.pop();
        out
    }

    /// The key a feed or a yield contributes under: the enclosing loops' keys.
    fn site_key(&self) -> Value {
        tuple_key(&self.loop_keys)
    }
}

/// Unit for no key, the key itself for one, and the tuple of them for several — the
/// iteration domain of a site under that many loops.
fn tuple_key(keys: &[Value]) -> Value {
    match keys {
        [] => Value::Unit,
        [k] => k.clone(),
        ks => Value::Record(
            ks.iter()
                .enumerate()
                .map(|(i, k)| (format!("_{i}"), k.clone()))
                .collect(),
        ),
    }
}

fn collection(entries: Vec<(Value, Value)>) -> Result<Collection, Error> {
    Collection::try_from_entries(entries)
        .map_err(|key| Error(format!("two entries share the key {key}")))
}

/// Run `source`, answering what each sink observed.
pub fn run(source: &str, sources: BTreeMap<String, Collection>) -> Result<Observations, Error> {
    let module = chl_parser::parse_module(source)
        .into_result()
        .map_err(|errors| Error(format!("parse error: {errors:?}")))?;
    let mut feed_sites = BTreeMap::new();
    collect_feed_sites(&module.body, &mut feed_sites);
    let mut feed_done_at = BTreeMap::new();
    for stmt in &module.body {
        let mut inner = BTreeMap::new();
        collect_feed_sites(std::slice::from_ref(stmt), &mut inner);
        for site in inner.into_values().flatten() {
            feed_done_at.insert(site, stmt.span.end);
        }
    }

    // Two `with` sites writing one variable commit in an order the program does not
    // determine, so every read and reply downstream of them has more than one right answer.
    let mut writers: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    collect_with_writes(&module.body, &mut writers);
    if let Some((name, _)) = writers.iter().find(|(_, sites)| sites.len() > 1) {
        return err(format!(
            "`{name}` is written by more than one `with` block, whose commit order is not \
             determined, which is not judgeable"
        ));
    }

    let mut interp = Interp::new(sources, feed_sites, feed_done_at);
    interp.exec_block(&module.body)?;

    interp
        .channels
        .iter()
        .filter(|(name, _)| interp.observed.contains(*name))
        .map(|(name, channel)| Ok((name.clone(), channel_value(channel)?)))
        .collect()
}

/// Every feed site in `body`, by the channel name it feeds, in source order.
fn collect_feed_sites(body: &[Spanned<Stmt>], out: &mut BTreeMap<String, Vec<usize>>) {
    for s in body {
        match &s.node {
            Stmt::Expr(e) => {
                if let Expr::Feed { target, value } = &e.node
                    && let Expr::Name(n) = &target.node
                {
                    out.entry(n.to_string()).or_default().push(value.span.start);
                }
            }
            Stmt::If {
                branches,
                else_body,
            } => {
                for b in branches {
                    collect_feed_sites(&b.body, out);
                }
                if let Some(body) = else_body {
                    collect_feed_sites(body, out);
                }
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_feed_sites(&a.body, out);
                }
            }
            Stmt::For { body, .. } | Stmt::FunctionDef { body, .. } | Stmt::With { body, .. } => {
                collect_feed_sites(body, out)
            }
            _ => {}
        }
    }
}

/// The `with` sites that write each variable, by the site's source position.
fn collect_with_writes(body: &[Spanned<Stmt>], out: &mut BTreeMap<String, Vec<usize>>) {
    for s in body {
        match &s.node {
            Stmt::With { body, .. } => {
                let mut names = BTreeSet::new();
                written_names(body, &mut names);
                for n in names {
                    out.entry(n).or_default().push(s.span.start);
                }
            }
            Stmt::If {
                branches,
                else_body,
            } => {
                for b in branches {
                    collect_with_writes(&b.body, out);
                }
                if let Some(body) = else_body {
                    collect_with_writes(body, out);
                }
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    collect_with_writes(&a.body, out);
                }
            }
            Stmt::For { body, .. } | Stmt::FunctionDef { body, .. } => {
                collect_with_writes(body, out)
            }
            _ => {}
        }
    }
}

/// The mutable variables `body` writes anywhere, by name.
fn written_names(body: &[Spanned<Stmt>], out: &mut BTreeSet<String>) {
    for s in body {
        match &s.node {
            Stmt::MutAssign { target, .. } | Stmt::AugAssign { target, .. } => match &target.node {
                AssignTarget::Name(n) => {
                    out.insert(n.to_string());
                }
                AssignTarget::Subscript { target, .. } => {
                    if let Expr::Name(n) = &target.node {
                        out.insert(n.to_string());
                    }
                }
                _ => {}
            },
            Stmt::If {
                branches,
                else_body,
            } => {
                for b in branches {
                    written_names(&b.body, out);
                }
                if let Some(body) = else_body {
                    written_names(body, out);
                }
            }
            Stmt::Match { arms, .. } => {
                for a in arms {
                    written_names(&a.body, out);
                }
            }
            Stmt::For { body, .. } => written_names(body, out),
            _ => {}
        }
    }
}

/// Whether an annotation sequences its mutable variable by `Txn`: `Mut(V, Txn)`.
fn is_txn_annotation(annotation: &TypeAnnotation) -> bool {
    matches!(&annotation.ty.node, Expr::Call { func, args }
        if matches!(&func.node, Expr::Name(n) if n == "Mut")
            && args.iter().any(|a| matches!(&a.node, Expr::Name(n) if n == "Txn")))
}

fn is_mut_annotation(annotation: &TypeAnnotation) -> bool {
    matches!(&annotation.ty.node, Expr::Call { func, .. }
        if matches!(&func.node, Expr::Name(n) if n == "Mut"))
}

impl Interp {
    fn exec_block(&mut self, stmts: &[Spanned<Stmt>]) -> Result<Option<Value>, Error> {
        for s in stmts {
            if let Some(v) = self.exec(s)? {
                return Ok(Some(v));
            }
        }
        Ok(None)
    }

    fn exec(&mut self, stmt: &Spanned<Stmt>) -> Result<Option<Value>, Error> {
        match &stmt.node {
            // `out = test_sink()` declares a sink; any other assignment binds a value.
            Stmt::Assign { target, value } => {
                let name = name_of(target)?;
                let is_sink = is_zero_arg_call(&value.node, "test_sink");
                if is_sink || is_zero_arg_call(&value.node, "defer") {
                    let sites = self.feed_sites.get(&name).cloned().unwrap_or_default();
                    self.channels.insert(
                        name.clone(),
                        Channel {
                            sites,
                            ..Channel::default()
                        },
                    );
                    if is_sink {
                        self.observed.insert(name);
                    }
                    return Ok(None);
                }
                let v = self.eval(value)?;
                self.bind(name, Slot::Val(v));
                Ok(None)
            }

            // The annotation states a type; nothing here reads types.
            Stmt::AnnAssign { target, value, .. } => {
                let name = name_of(target)?;
                let v = self.eval(value)?;
                self.bind(name, Slot::Val(v));
                Ok(None)
            }

            // `x := e` writes the mutable variable `x` resolves to, or declares one in the
            // current scope when `x` resolves to none; `m[k] := e` writes one entry of one.
            // Inside a block the write is immediately visible to later reads in the same
            // block, which is what read-your-writes means, and it is what decides the
            // block commits.
            Stmt::MutAssign {
                target,
                annotation,
                value,
            } => {
                let v = self.eval(value)?;
                match &target.node {
                    AssignTarget::Name(n) => match self.mut_cell(n) {
                        Some(cell) => self.write(&cell, v),
                        None => {
                            let txn = annotation.as_ref().is_some_and(is_txn_annotation);
                            let cell = Rc::new(RefCell::new(MutCell { value: v, txn }));
                            self.bind(n.to_string(), Slot::Mut(cell));
                        }
                    },
                    AssignTarget::Subscript { target, index } => {
                        let Expr::Name(n) = &target.node else {
                            return err("a keyed write names a mutable variable");
                        };
                        let key = self.eval(index)?;
                        let Some(cell) = self.mut_cell(n) else {
                            return err(format!("`{n}` is not a mutable variable"));
                        };
                        let Value::Collection(c) = cell.borrow().value.clone() else {
                            return err(format!("`{n}` is not a mutable collection"));
                        };
                        // Last write wins per key, in place; a key not yet present is added.
                        let mut entries = c.entries().to_vec();
                        match entries.iter_mut().find(|(k, _)| *k == key) {
                            Some(entry) => entry.1 = v,
                            None => entries.push((key, v)),
                        }
                        self.write(&cell, Value::Collection(collection(entries)?));
                    }
                    other => return err(format!("unsupported write target: {other:?}")),
                }
                Ok(None)
            }

            // `x += e` is the compound form of `x := x + e`, so it writes a mutable variable
            // and nothing else.
            Stmt::AugAssign { target, op, value } => {
                let name = name_of(target)?;
                let Some(cell) = self.mut_cell(&name) else {
                    return err(format!("`{name}` is not a mutable variable"));
                };
                let current = self.read_mut(&name, &cell)?;
                let rhs = self.eval(value)?;
                let updated = binop(
                    match op {
                        AugOp::Add => BinOp::Add,
                        AugOp::Sub => BinOp::Sub,
                        AugOp::Mul => BinOp::Mul,
                        AugOp::FloorDiv => BinOp::FloorDiv,
                    },
                    current,
                    rhs,
                )?;
                self.write(&cell, updated);
                Ok(None)
            }

            // `out <<= e` defines the channel as `e` outright, rather than contributing
            // one entry to it.
            Stmt::Define { target, value } => {
                let name = name_of(target)?;
                let v = self.eval(value)?;
                match self.channels.get_mut(&name) {
                    Some(channel) => {
                        if channel.defined.is_some() || !channel.sites.is_empty() {
                            return err(format!(
                                "`{name}` is defined twice, or both fed and defined"
                            ));
                        }
                        channel.defined = Some(v);
                    }
                    None => self.bind(name, Slot::Val(v)),
                }
                Ok(None)
            }

            Stmt::If {
                branches,
                else_body,
            } => match self.select_branch(branches, else_body)? {
                Some(body) => self.exec_block(&body),
                None => Ok(None),
            },

            // Tag dispatch: the first arm whose tag matches, or a wildcard arm.
            Stmt::Match { scrutinee, arms } => {
                let (bound, body) = self.match_arm(scrutinee, arms)?;
                let body = body.to_vec();
                self.scoped(|me| {
                    if let Some((n, v)) = bound {
                        me.bind(n, Slot::Val(v));
                    }
                    me.exec_block(&body)
                })
            }

            Stmt::FunctionDef {
                name, params, body, ..
            } => {
                let function = Function {
                    params: params
                        .iter()
                        .map(|p| {
                            let by_ref = p.annotation.as_ref().is_some_and(is_mut_annotation);
                            (p.name.to_string(), by_ref)
                        })
                        .collect(),
                    body: body.clone(),
                    env: self.captured_scopes(),
                };
                self.functions.insert(name.to_string(), function);
                Ok(None)
            }

            Stmt::Return(value) => match value {
                Some(e) => Ok(Some(self.eval(e)?)),
                None => Ok(Some(Value::Unit)),
            },

            Stmt::For {
                target, iter, body, ..
            } => {
                let name = match &target.node {
                    AssignTarget::Name(n) => n.to_string(),
                    other => return err(format!("unsupported loop target: {other:?}")),
                };
                let source = self.eval(iter)?;
                let Value::Collection(c) = source else {
                    return err("a `for` loop iterates a collection");
                };
                for (key, elem) in c.entries().to_vec() {
                    // The loop's key extends the feed site's key: a contribution from inside
                    // this body lands under the position its element came from.
                    self.loop_keys.push(key);
                    let returned = self.scoped(|me| {
                        me.bind(name.clone(), Slot::Val(elem));
                        me.exec_block(body)
                    });
                    self.loop_keys.pop();
                    if let Some(v) = returned? {
                        return Ok(Some(v));
                    }
                }
                Ok(None)
            }

            Stmt::Expr(e) => {
                // A feed is the only expression statement that does anything; a trailing
                // bare expression is not an observable.
                if let Expr::Feed { target, value } = &e.node {
                    self.feed(target, value)?;
                    return Ok(None);
                }
                if let Expr::Yield(inner) = &e.node {
                    if self.yielded.is_none() {
                        return err("`yield` outside a generator");
                    }
                    let key = self.site_key();
                    let v = self.eval(inner)?;
                    self.yielded.as_mut().expect("checked").push((key, v));
                    return Ok(None);
                }
                self.eval(e).map(|_| None)
            }

            // `with begin():` — one commit record per block, at the next commit time, or none if
            // the block denied.
            Stmt::With {
                binding,
                context,
                body,
            } => {
                if binding.is_some() {
                    return err("the `with t = begin():` transaction handle is not supported");
                }
                if !is_zero_arg_call(&context.node, "begin") {
                    return err("the only transaction context is `begin()`");
                }
                if self.txn.is_some() {
                    return err("nested `with begin():` transactions are not supported");
                }
                let mut writes = BTreeSet::new();
                written_names(body, &mut writes);
                self.txn = Some(TxnFrame {
                    wrote: false,
                    writes,
                    replies: Vec::new(),
                });
                let outcome = self.scoped(|me| me.exec_block(body));
                let frame = self.txn.take().expect("installed above");
                outcome?;

                if !frame.wrote && frame.replies.is_empty() {
                    // Denied: no write, no reply, no commit time.
                    return Ok(None);
                }
                self.commit_time += 1;
                let at = Value::CommitTime(self.commit_time);
                for (channel, site, value) in frame.replies {
                    self.channels
                        .get_mut(&channel)
                        .expect("a reply names an open channel")
                        .fed
                        .push((site, at.clone(), value));
                }
                Ok(None)
            }

            Stmt::Pass => Ok(None),
            other => err(format!("unsupported statement: {other:?}")),
        }
    }

    /// The scopes a function defined here closes over: every value as it stands now
    /// ("4.1 `def` — function definition" captures values at definition time), except a
    /// `Txn` store, which a function reaches through the store itself.
    fn captured_scopes(&self) -> Vec<Scope> {
        self.scopes
            .iter()
            .map(|scope| {
                scope
                    .iter()
                    .map(|(n, slot)| {
                        let captured = match slot {
                            Slot::Mut(cell) if !cell.borrow().txn => {
                                Slot::Val(cell.borrow().value.clone())
                            }
                            other => other.clone(),
                        };
                        (n.clone(), captured)
                    })
                    .collect()
            })
            .collect()
    }

    fn write(&mut self, cell: &Rc<RefCell<MutCell>>, value: Value) {
        cell.borrow_mut().value = value;
        if let Some(frame) = self.txn.as_mut() {
            frame.wrote = true;
        }
    }

    /// Read a mutable variable where "8.3 Reads" makes the read determinate, and refuse
    /// where it does not: a `Txn` variable outside a block, or inside one that does not
    /// write it.
    fn read_mut(&self, name: &str, cell: &Rc<RefCell<MutCell>>) -> Result<Value, Error> {
        let cell = cell.borrow();
        if cell.txn {
            match &self.txn {
                None => return err(format!("`{name}` is a `Txn` variable read outside a block")),
                Some(frame) if !frame.writes.contains(name) => {
                    return err(format!(
                        "`{name}` is read as of an arbitrary commit position, which is not judgeable"
                    ));
                }
                Some(_) => {}
            }
        }
        Ok(cell.value.clone())
    }

    /// The body an `if`/`elif`/`else` chain selects, if any.
    fn select_branch(
        &mut self,
        branches: &[IfBranch],
        else_body: &Option<Vec<Spanned<Stmt>>>,
    ) -> Result<Option<Vec<Spanned<Stmt>>>, Error> {
        for branch in branches {
            let Value::Bool(taken) = self.eval(&branch.cond)? else {
                return err("an `if` condition is a boolean");
            };
            if taken {
                return Ok(Some(branch.body.clone()));
            }
        }
        Ok(else_body.clone())
    }

    fn feed(&mut self, target: &Spanned<Expr>, value: &Spanned<Expr>) -> Result<(), Error> {
        let Expr::Name(name) = &target.node else {
            return err("a feed's target is a name");
        };
        let name = name.to_string();
        if !self.channels.contains_key(&name) {
            return err(format!("`{name}` is not a channel"));
        }
        let contributed = self.eval(value)?;
        // The feed's source position identifies the site: two `<<` in one program are two
        // places whatever they write.
        let site = value.span.start;
        if let Some(frame) = self.txn.as_mut() {
            // A reply rides its block's commit, so it is indexed by commit time, not by
            // the iteration that produced it. The commit time is not known until the block
            // commits, so the reply waits here.
            frame.replies.push((name, site, contributed));
            return Ok(());
        }
        let key = self.site_key();
        self.channels
            .get_mut(&name)
            .expect("checked above")
            .fed
            .push((site, key, contributed));
        Ok(())
    }
}

impl Interp {
    /// The value a block denotes: its statements run, and its last one is an expression
    /// whose value is the block's. `return` is the other way out.
    fn block_value(&mut self, body: &[Spanned<Stmt>]) -> Result<Value, Error> {
        let Some((last, rest)) = body.split_last() else {
            return err("an empty block has no value");
        };
        if let Some(v) = self.exec_block(rest)? {
            return Ok(v);
        }
        match &last.node {
            Stmt::Expr(e) => self.eval(e),
            Stmt::Return(Some(e)) => self.eval(e),
            other => err(format!(
                "a block ends with {other:?}, which denotes no value"
            )),
        }
    }

    /// The arm a `match` selects, with its payload bound.
    fn match_arm<'a>(
        &mut self,
        scrutinee: &Spanned<Expr>,
        arms: &'a [chl_parser::ast::MatchArm],
    ) -> Result<Selected<'a>, Error> {
        let v = self.eval(scrutinee)?;
        let Value::Variant { tag, payload } = v else {
            return err("`match` dispatches on a variant");
        };
        for arm in arms {
            let Some(pattern) = &arm.pattern else {
                return Ok((None, &arm.body));
            };
            if pattern.tag.as_str() != tag {
                continue;
            }
            let bound = match &pattern.payload {
                PayloadPattern::Named(n) => Some((n.to_string(), (*payload).clone())),
                PayloadPattern::Ignored | PayloadPattern::Absent => None,
            };
            return Ok((bound, &arm.body));
        }
        err(format!("no `match` arm for tag `{tag}"))
    }
}

/// What a channel holds: the value a `<<=` defined it as, or its contributions keyed as
/// the channel's domain keys them.
///
/// One feed site leaves the keys alone. Several make the channel a union of them, so each
/// key is tagged by the site's position among the channel's sites in source order.
fn channel_value(channel: &Channel) -> Result<Value, Error> {
    if let Some(v) = &channel.defined {
        return Ok(v.clone());
    }
    let mut entries = Vec::with_capacity(channel.fed.len());
    for (site, key, value) in &channel.fed {
        let key = if channel.sites.len() > 1 {
            let tag = channel
                .sites
                .iter()
                .position(|s| s == site)
                .expect("every site that fires was collected from the program text");
            Value::Variant {
                tag: tag.to_string(),
                payload: Box::new(key.clone()),
            }
        } else {
            key.clone()
        };
        entries.push((key, value.clone()));
    }
    Ok(Value::Collection(collection(entries)?))
}

/// The arm a `match` chose: the payload it binds, if any, and the body to run.
type Selected<'a> = (Option<(String, Value)>, &'a [Spanned<Stmt>]);

/// The single name an assignment target binds.
fn name_of(target: &Spanned<AssignTarget>) -> Result<String, Error> {
    match &target.node {
        AssignTarget::Name(n) => Ok(n.to_string()),
        other => err(format!("unsupported assignment target: {other:?}")),
    }
}

fn is_zero_arg_call(e: &Expr, name: &str) -> bool {
    matches!(e, Expr::Call { func, args }
        if args.is_empty() && matches!(&func.node, Expr::Name(n) if n == name))
}

/// Whether a body yields, which is what makes a `def` a generator.
fn contains_yield(body: &[Spanned<Stmt>]) -> bool {
    body.iter().any(|s| match &s.node {
        Stmt::Expr(e) => matches!(e.node, Expr::Yield(_)),
        Stmt::For { body, .. } => contains_yield(body),
        Stmt::If {
            branches,
            else_body,
        } => {
            branches.iter().any(|b| contains_yield(&b.body))
                || else_body.as_deref().is_some_and(contains_yield)
        }
        Stmt::Match { arms, .. } => arms.iter().any(|a| contains_yield(&a.body)),
        _ => false,
    })
}

impl Interp {
    fn eval(&mut self, e: &Spanned<Expr>) -> Result<Value, Error> {
        match &e.node {
            Expr::Lit(Lit::Int(i)) => Ok(Value::Int(*i)),
            Expr::Lit(Lit::String(s)) => Ok(Value::Str(s.clone())),
            Expr::Lit(Lit::Bool(b)) => Ok(Value::Bool(*b)),

            Expr::Name(n) => {
                if let Some(channel) = self.channels.get(n.as_str()) {
                    if let Some(site) = channel.sites.iter().find(|s| {
                        self.feed_done_at
                            .get(s)
                            .is_none_or(|end| *end > e.span.start)
                    }) {
                        return err(format!(
                            "`{n}` is read before its feed at {site} has run, and the read \
                             denotes the whole collection"
                        ));
                    }
                    return channel_value(channel);
                }
                match self.slot(n) {
                    Some(Slot::Val(v)) => Ok(v.clone()),
                    Some(Slot::Mut(cell)) => {
                        let cell = cell.clone();
                        self.read_mut(n, &cell)
                    }
                    None => err(format!("unbound name: {n}")),
                }
            }

            Expr::List(items) => {
                let mut out = Vec::with_capacity(items.len());
                for it in items {
                    out.push(self.eval(it)?);
                }
                Ok(Value::Collection(Collection::from_list(out)))
            }

            Expr::Record(fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    out.push((f.name.to_string(), self.eval(&f.value)?));
                }
                Ok(Value::Record(out))
            }

            Expr::Attribute { target, attr, .. } => {
                let v = self.eval(target)?;
                let Value::Record(fields) = v else {
                    return err(format!("field access `.{attr}` on a non-record"));
                };
                // A positional component is the field the tuple stored it under.
                let wanted = match attr.parse::<usize>() {
                    Ok(i) => format!("_{i}"),
                    Err(_) => attr.to_string(),
                };
                fields
                    .into_iter()
                    .find(|(n, _)| *n == wanted)
                    .map(|(_, v)| v)
                    .ok_or_else(|| Error(format!("no field `{attr}`")))
            }

            Expr::VariantCtor { tag, payload, .. } => {
                let inner = match payload {
                    None => Value::Unit,
                    Some(VariantPayload::Term(inner)) => self.eval(inner)?,
                    Some(p) => return err(format!("unsupported variant payload: {p:?}")),
                };
                Ok(Value::Variant {
                    tag: tag.to_string(),
                    payload: Box::new(inner),
                })
            }

            Expr::UnaryOp { op, operand } => {
                let v = self.eval(operand)?;
                match (op, v) {
                    (UnaryOp::Neg, Value::Int(i)) => i
                        .checked_neg()
                        .map(Value::Int)
                        .ok_or_else(|| Error(format!("-({i}) is not defined"))),
                    (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    (op, v) => err(format!("unsupported unary {op:?} on {v}")),
                }
            }

            Expr::BinOp { op, left, right } => {
                let (l, r) = (self.eval(left)?, self.eval(right)?);
                binop(*op, l, r)
            }

            Expr::Compare {
                left,
                ops,
                comparators,
            } => {
                let mut prev = self.eval(left)?;
                for (op, rhs) in ops.iter().zip(comparators) {
                    let next = self.eval(rhs)?;
                    let Value::Bool(held) = compare(*op, prev, next.clone())? else {
                        return err("a comparison answers a boolean");
                    };
                    if !held {
                        return Ok(Value::Bool(false));
                    }
                    prev = next;
                }
                Ok(Value::Bool(true))
            }

            // Short-circuiting, so an operand past the decisive one is never evaluated.
            Expr::BoolOp { op, operands } => {
                let mut last = matches!(op, BoolOp::And);
                for operand in operands {
                    let Value::Bool(b) = self.eval(operand)? else {
                        return err("a boolean operator takes booleans");
                    };
                    last = b;
                    match op {
                        BoolOp::And if !b => return Ok(Value::Bool(false)),
                        BoolOp::Or if b => return Ok(Value::Bool(true)),
                        _ => {}
                    }
                }
                Ok(Value::Bool(last))
            }

            Expr::IfExp {
                cond,
                then_expr,
                else_expr,
            } => {
                let Value::Bool(c) = self.eval(cond)? else {
                    return err("a conditional's test is a boolean");
                };
                if c {
                    self.eval(then_expr)
                } else {
                    self.eval(else_expr)
                }
            }

            Expr::ListComp(comp) => {
                let mut out = Vec::new();
                self.comprehend(&comp.clauses, &comp.element, &mut Vec::new(), &mut out)?;
                Ok(Value::Collection(collection(out)?))
            }

            // A tuple is a record over positional names, which is how the compiler spells
            // one too (`tuple_field(0)` is `_0`).
            Expr::Tuple(items) => {
                let mut fields = Vec::with_capacity(items.len());
                for (i, it) in items.iter().enumerate() {
                    fields.push((format!("_{i}"), self.eval(it)?));
                }
                Ok(Value::Record(fields))
            }

            Expr::Subscript { target, index, .. } => {
                let t = self.eval(target)?;
                let k = self.eval(index)?;
                match t {
                    Value::Collection(c) => c
                        .entries()
                        .iter()
                        .find(|(key, _)| *key == k)
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| Error(format!("no entry at key {k}"))),
                    Value::Record(fields) => {
                        let Value::Int(i) = k else {
                            return err("a product is subscripted by position");
                        };
                        fields
                            .into_iter()
                            .find(|(n, _)| *n == format!("_{i}"))
                            .map(|(_, v)| v)
                            .ok_or_else(|| Error(format!("no component _{i}")))
                    }
                    other => err(format!("cannot subscript {other}")),
                }
            }

            // A statement in expression position: `match` and `if`/`else` denote the value
            // of the branch they take.
            Expr::Block(stmt) => match &stmt.node {
                Stmt::Match { scrutinee, arms } => {
                    let (bound, body) = self.match_arm(scrutinee, arms)?;
                    let body = body.to_vec();
                    self.scoped(|me| {
                        if let Some((n, v)) = bound {
                            me.bind(n, Slot::Val(v));
                        }
                        me.block_value(&body)
                    })
                }
                Stmt::If {
                    branches,
                    else_body,
                } => match self.select_branch(branches, else_body)? {
                    Some(body) => self.scoped(|me| me.block_value(&body)),
                    None => err("an `if` with no `else` denotes no value"),
                },
                other => err(format!("{other:?} in expression position")),
            },

            Expr::Call { func, args } => self.call(func, args),

            other => err(format!("unsupported expression: {other:?}")),
        }
    }

    /// The builtins the corpus reaches, plus a zero-argument call naming a source.
    ///
    /// A lambda is applied where it is written rather than becoming a value: nothing in
    /// CHL observes a function, so the comparison domain has no reason to carry one.
    fn call(&mut self, func: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Result<Value, Error> {
        let Expr::Name(name) = &func.node else {
            return err("only a named function can be called");
        };
        // A user function shadows a builtin of the same name: the nearest binding wins
        // ("3.2 Names").
        if let Some(function) = self.functions.get(name.as_str()).cloned() {
            return self.call_user(name, function, args);
        }

        match (name.as_str(), args.len()) {
            // `await_final` consumes its variable ("8.6 `await_final`"): no write may name
            // it afterwards, so its current value is its final one.
            ("await_final", 1) => {
                let Expr::Name(n) = &args[0].node else {
                    return err("`await_final` takes a mutable variable");
                };
                let Some(cell) = self.mut_cell(n) else {
                    return err(format!("`{n}` is not a mutable variable"));
                };
                Ok(cell.borrow().value.clone())
            }

            // A map is written as its entries; `box` marks a value as a whole rather than
            // a collection to iterate, which changes nothing about what it is.
            ("map", 1) => {
                let Value::Collection(pairs) = self.eval(&args[0])? else {
                    return err("`map` takes a collection of pairs");
                };
                let mut entries = Vec::with_capacity(pairs.len());
                for (_, pair) in pairs.entries() {
                    let Value::Record(fields) = pair else {
                        return err("`map` takes a collection of pairs");
                    };
                    let get = |n: &str| {
                        fields
                            .iter()
                            .find(|(f, _)| f == n)
                            .map(|(_, v)| v.clone())
                            .ok_or_else(|| Error(format!("a pair has no component {n}")))
                    };
                    entries.push((get("_0")?, get("_1")?));
                }
                Ok(Value::Collection(collection(entries)?))
            }

            ("box", 1) => self.eval(&args[0]),

            ("max", 1) => {
                let Value::Collection(c) = self.eval(&args[0])? else {
                    return err("`max` takes a collection");
                };
                let mut best: Option<i64> = None;
                for (_, v) in c.entries() {
                    let Value::Int(i) = v else {
                        return err("`max` takes a collection of integers");
                    };
                    best = Some(best.map_or(*i, |b: i64| b.max(*i)));
                }
                best.map(Value::Int)
                    .ok_or_else(|| Error("`max` of an empty collection is not defined".into()))
            }

            (name, 0) => match self.sources.get(name) {
                Some(c) => Ok(Value::Collection(c.clone())),
                None => err(format!("unknown zero-argument function: {name}")),
            },

            ("sum", 1) => {
                let Value::Collection(c) = self.eval(&args[0])? else {
                    return err("`sum` takes a collection");
                };
                let mut total = Value::Int(0);
                for (_, v) in c.entries() {
                    let Value::Int(_) = v else {
                        return err("`sum` takes a collection of integers");
                    };
                    total = binop(BinOp::Add, total, v.clone())?;
                }
                Ok(total)
            }

            // `groupby(xs, f)` is keyed by the group key, and each group holds its members
            // under the keys they had in `xs`.
            ("groupby", 2) => {
                let Value::Collection(c) = self.eval(&args[0])? else {
                    return err("`groupby` takes a collection");
                };
                let mut groups: Vec<(Value, Vec<(Value, Value)>)> = Vec::new();
                for (key, elem) in c.entries().to_vec() {
                    let gk = self.apply(&args[1], elem.clone())?;
                    match groups.iter_mut().find(|(k, _)| *k == gk) {
                        Some((_, members)) => members.push((key, elem)),
                        None => groups.push((gk, vec![(key, elem)])),
                    }
                }
                let mut entries = Vec::with_capacity(groups.len());
                for (k, members) in groups {
                    entries.push((k, Value::Collection(collection(members)?)));
                }
                Ok(Value::Collection(collection(entries)?))
            }

            (name, n) => err(format!("unknown function `{name}` of {n} argument(s)")),
        }
    }

    /// Call a user function: its body runs against the scopes it was defined in, with a
    /// `Mut` parameter aliasing its argument's cell and every other parameter bound to a
    /// value.
    fn call_user(
        &mut self,
        name: &str,
        function: Function,
        args: &[Spanned<Expr>],
    ) -> Result<Value, Error> {
        if function.params.len() != args.len() {
            return err(format!(
                "`{name}` takes {} argument(s), given {}",
                function.params.len(),
                args.len()
            ));
        }
        let mut params = Scope::with_capacity(args.len());
        for ((param, by_ref), arg) in function.params.iter().zip(args) {
            let slot = if *by_ref {
                let Expr::Name(n) = &arg.node else {
                    return err(format!("`{param}` takes a mutable variable"));
                };
                let Some(cell) = self.mut_cell(n) else {
                    return err(format!("`{n}` is not a mutable variable"));
                };
                Slot::Mut(cell)
            } else {
                Slot::Val(self.eval(arg)?)
            };
            params.push((param.clone(), slot));
        }

        let mut env = function.env;
        env.push(params);
        let caller = std::mem::replace(&mut self.scopes, env);
        let outcome = if contains_yield(&function.body) {
            // A generator denotes the collection of what it yielded, keyed by its own
            // loops' positions.
            let outer_yielded = self.yielded.replace(Vec::new());
            let outer_keys = std::mem::take(&mut self.loop_keys);
            let ran = self.exec_block(&function.body);
            let collected =
                std::mem::replace(&mut self.yielded, outer_yielded).expect("installed above");
            self.loop_keys = outer_keys;
            ran.and_then(|_| collection(collected).map(Value::Collection))
        } else if matches!(
            function.body.last().map(|s| &s.node),
            Some(Stmt::Expr(_) | Stmt::Return(_))
        ) {
            self.block_value(&function.body)
        } else {
            // A body ending in a statement, such as a write through a `Mut` parameter, is
            // run for its effects and denotes unit.
            self.exec_block(&function.body)
                .map(|returned| returned.unwrap_or(Value::Unit))
        };
        self.scopes = caller;
        outcome
    }

    /// Apply a lambda written at the call site.
    fn apply(&mut self, lambda: &Spanned<Expr>, arg: Value) -> Result<Value, Error> {
        let Expr::Lambda { params, body } = &lambda.node else {
            return err("expected a lambda");
        };
        let [param] = params.as_slice() else {
            return err("expected a one-parameter lambda");
        };
        let name = param.name.to_string();
        self.scoped(|me| {
            me.bind(name, Slot::Val(arg));
            me.eval(body)
        })
    }

    /// Walk a comprehension's clauses, collecting `key -> element` for each surviving
    /// binding. The key is the position the element came from — the tuple of positions
    /// under several `for` clauses — so a filter keeps the positions of its survivors
    /// rather than renumbering them.
    fn comprehend(
        &mut self,
        clauses: &[CompClause],
        element: &Spanned<Expr>,
        keys: &mut Vec<Value>,
        out: &mut Vec<(Value, Value)>,
    ) -> Result<(), Error> {
        match clauses.split_first() {
            None => {
                let v = self.eval(element)?;
                out.push((tuple_key(keys), v));
                Ok(())
            }
            Some((CompClause::If(guard), rest)) => {
                let Value::Bool(keep) = self.eval(guard)? else {
                    return err("a comprehension guard is a boolean");
                };
                if keep {
                    self.comprehend(rest, element, keys, out)?;
                }
                Ok(())
            }
            Some((CompClause::For { target, iter }, rest)) => {
                let name = match &target.node {
                    AssignTarget::Name(n) => n.to_string(),
                    other => return err(format!("unsupported comprehension target: {other:?}")),
                };
                let Value::Collection(c) = self.eval(iter)? else {
                    return err("a comprehension iterates a collection");
                };
                for (key, elem) in c.entries().to_vec() {
                    keys.push(key);
                    let walked = self.scoped(|me| {
                        me.bind(name.clone(), Slot::Val(elem));
                        me.comprehend(rest, element, keys, out)
                    });
                    keys.pop();
                    walked?;
                }
                Ok(())
            }
        }
    }
}

/// Integer division rounding toward negative infinity, the `//` of "3.3 Arithmetic and
/// logical operators".
fn floor_div(a: i64, b: i64) -> Option<i64> {
    let q = a.checked_div(b)?;
    let rounds_down = a % b != 0 && ((a < 0) != (b < 0));
    Some(if rounds_down { q - 1 } else { q })
}

fn binop(op: BinOp, l: Value, r: Value) -> Result<Value, Error> {
    let int = |v: Option<i64>| {
        v.map(Value::Int)
            .ok_or_else(|| Error(format!("{l} {op:?} {r} is not defined")))
    };
    match (op, &l, &r) {
        (BinOp::Add | BinOp::AddRefined, Value::Int(a), Value::Int(b)) => int(a.checked_add(*b)),
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => int(a.checked_sub(*b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => int(a.checked_mul(*b)),
        (BinOp::FloorDiv, Value::Int(a), Value::Int(b)) => int(floor_div(*a, *b)),
        (BinOp::LogicalAnd, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a && *b)),
        (BinOp::LogicalOr, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a || *b)),
        (BinOp::LogicalXor, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a != b)),
        (BinOp::CollectionUnion, Value::Collection(a), Value::Collection(b)) => {
            let tagged = |i: usize, c: &Collection| {
                c.entries()
                    .iter()
                    .map(|(k, v)| {
                        (
                            Value::Variant {
                                tag: i.to_string(),
                                payload: Box::new(k.clone()),
                            },
                            v.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
            };
            let mut out = tagged(0, a);
            out.extend(tagged(1, b));
            Ok(Value::Collection(collection(out)?))
        }
        _ => err(format!("unsupported {op:?} on {l} and {r}")),
    }
}

fn compare(op: CmpOp, l: Value, r: Value) -> Result<Value, Error> {
    let ord = match (&l, &r) {
        (Value::Int(a), Value::Int(b)) => a.cmp(b),
        (Value::Str(a), Value::Str(b)) => a.cmp(b),
        _ => {
            return match op {
                CmpOp::Eq => Ok(Value::Bool(l == r)),
                CmpOp::NotEq => Ok(Value::Bool(l != r)),
                _ => err(format!("unsupported {op:?} on {l} and {r}")),
            };
        }
    };
    Ok(Value::Bool(match op {
        CmpOp::Eq => ord.is_eq(),
        CmpOp::NotEq => ord.is_ne(),
        CmpOp::Lt => ord.is_lt(),
        CmpOp::LtE => ord.is_le(),
        CmpOp::Gt => ord.is_gt(),
        CmpOp::GtE => ord.is_ge(),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    fn out(source: &str) -> Value {
        run(source, BTreeMap::new())
            .expect("the program runs")
            .remove("out")
            .expect("sink `out`")
    }

    fn refused(source: &str) -> String {
        run(source, BTreeMap::new())
            .expect_err("the program is refused")
            .0
    }

    #[test]
    fn floor_division_rounds_toward_negative_infinity() {
        assert_eq!(floor_div(7, 2), Some(3));
        assert_eq!(floor_div(7, -2), Some(-4));
        assert_eq!(floor_div(-7, 2), Some(-4));
        assert_eq!(floor_div(-7, -2), Some(3));
        assert_eq!(floor_div(6, -2), Some(-3));
        assert_eq!(floor_div(1, 0), None);
    }

    #[test]
    fn overflow_is_not_defined() {
        let e = refused(indoc! {r#"
            out = test_sink()
            out << 9223372036854775807 + 1
        "#});
        assert!(e.contains("is not defined"), "{e}");
    }

    #[test]
    fn a_two_clause_comprehension_is_keyed_by_the_pair() {
        let v = out(indoc! {r#"
            out = test_sink()
            out << [x * 10 + y for x in [1, 2] for y in [1, 2]]
        "#});
        assert_eq!(
            v.to_string(),
            "[() -> [(_0: 0, _1: 0) -> 11, (_0: 0, _1: 1) -> 12, \
             (_0: 1, _1: 0) -> 21, (_0: 1, _1: 1) -> 22]]"
        );
    }

    #[test]
    fn two_straight_line_yields_share_a_key_and_are_refused() {
        let e = refused(indoc! {r#"
            def g():
                yield 1
                yield 2

            out = test_sink()
            out << max(g())
        "#});
        assert!(e.contains("share the key"), "{e}");
    }

    #[test]
    fn a_define_is_the_channel_value() {
        let v = out(indoc! {r#"
            out = test_sink()
            out <<= [1, 2, 3]
        "#});
        assert_eq!(v.to_string(), "[1, 2, 3]");
    }

    /// Tagging is a property of the program text: the untaken site still makes the
    /// channel a union.
    #[test]
    fn a_site_that_never_fires_still_tags_the_channel() {
        let v = out(indoc! {r#"
            out = test_sink()
            out << 1
            if 1 > 2:
                out << 2
        "#});
        assert_eq!(v.to_string(), "[`0(()) -> 1]");
    }

    #[test]
    fn an_augmented_write_is_a_write() {
        let v = out(indoc! {r#"
            out = test_sink()
            b: Mut(Int, Txn) := 0
            for r in [2, 3]:
                with begin():
                    b += r
                    out << b
        "#});
        assert_eq!(v.to_string(), "[t1 -> 2, t2 -> 5]");
    }

    #[test]
    fn two_with_sites_writing_one_variable_are_refused() {
        let e = refused(indoc! {r#"
            out = test_sink()
            b: Mut(Int, Txn) := 0
            for r in [2, 3]:
                with begin():
                    b += r
            with begin():
                b := b
                out << b
        "#});
        assert!(e.contains("more than one `with` block"), "{e}");
    }

    #[test]
    fn a_channel_read_before_its_feeds_run_is_refused() {
        let e = refused(indoc! {r#"
            ch = defer()
            out = test_sink()
            out << sum(ch)
            for x in [1, 2, 3]:
                ch << x
        "#});
        assert!(e.contains("is read before its feed"), "{e}");
    }

    #[test]
    fn a_function_writing_through_a_mut_parameter_denotes_unit() {
        let v = out(indoc! {r#"
            def bump(c: Mut(Int)):
                c += 1

            n := 1
            bump(n)
            bump(n)
            out = test_sink()
            out << n
        "#});
        assert_eq!(v.to_string(), "[() -> 3]");
    }

    #[test]
    fn an_augmented_write_to_an_immutable_name_is_refused() {
        let e = refused(indoc! {r#"
            x = 1
            x += 1
        "#});
        assert!(e.contains("not a mutable variable"), "{e}");
    }

    #[test]
    fn a_function_resolves_names_where_it_was_defined() {
        let v = out(indoc! {r#"
            base = 10

            def bump(n):
                n + base

            base = 20
            out = test_sink()
            for base in [100]:
                out << bump(3)
        "#});
        assert_eq!(v.to_string(), "[13]");
    }

    #[test]
    fn a_function_captures_a_mutable_variable_s_value_at_definition() {
        let v = out(indoc! {r#"
            c := 1

            def f(n):
                n + c

            c := 5
            out = test_sink()
            out << f(0)
        "#});
        assert_eq!(v.to_string(), "[() -> 1]");
    }

    #[test]
    fn a_txn_variable_read_in_a_block_that_does_not_write_it_is_refused() {
        let e = refused(indoc! {r#"
            out = test_sink()
            pool: Mut(Int, Txn) := 100
            for r in [1]:
                with begin():
                    out << pool
        "#});
        assert!(e.contains("not judgeable"), "{e}");
    }

    #[test]
    fn a_parse_error_is_refused_rather_than_recovered() {
        let e = refused(indoc! {r#"
            out = test_sink()
            out << (1 +
        "#});
        assert!(e.contains("parse error"), "{e}");
    }
}
