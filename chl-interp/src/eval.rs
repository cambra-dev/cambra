//! Evaluating a CHL program to what each of its sinks observed.
//!
//! A program's observable is its sinks, not a returned value, so evaluation answers a map
//! from sink name to the collection of contributions that sink received. A trailing bare
//! expression is a test convenience in the compiler and denotes nothing here.
//!
//! **A feed nests.** The channel a sink reads is indexed by the *feed site's* iteration
//! domain — unit where the site does not iterate — and whatever was fed sits under that key
//! whatever its shape. So `out << [2, 4, 6]` is one contribution holding a three-element
//! collection, and `for x in xs: out << e` is one contribution per iteration under the key
//! `x` was drawn from.

use std::collections::BTreeMap;

use chl_parser::ast::{
    AssignTarget, AugOp, BinOp, BoolOp, CmpOp, CompClause, Expr, Lit, PayloadPattern, Spanned,
    Stmt, UnaryOp, VariantPayload,
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

/// The key a feed contributes under: the enclosing loop's key, or unit at a site that does
/// not iterate.
#[derive(Clone)]
struct FeedSite(Value);

/// A `with begin():` block in progress.
///
/// Whether the block commits is decided by what it did, not by a separate flag: a block
/// that wrote nothing and replied nothing took no path to a write, which is a denial. So
/// there is no state where a block has real writes and no commit.
#[derive(Default)]
struct TxnFrame {
    wrote: bool,
    /// Replies fed inside the block, held until the block commits and its tick is known.
    replies: Vec<(String, usize, Value)>,
}

pub struct Interp {
    /// Lexical scopes, innermost last.
    scopes: Vec<Vec<(String, Value)>>,
    /// Contributions per open channel: the feed site that made each, its key, and its
    /// value. `defer()` and `test_sink()` both open a channel; only a test sink is
    /// observed.
    ///
    /// The site is carried because a channel fed from more than one place is a union of
    /// those places, and its keys are tagged by which one — so the site is part of the
    /// key, not bookkeeping. A channel with one site has nothing to tell apart and keeps
    /// its bare keys.
    sinks: BTreeMap<String, Vec<(usize, Value, Value)>>,
    /// The channels a `test_sink()` opened, which are what `run` answers with.
    observed: std::collections::BTreeSet<String>,
    /// The values a generator has yielded, while one is running.
    yielded: Option<Vec<(Value, Value)>>,
    /// The commit ticks a transaction block has consumed. Ticks are dense and 1-based: a
    /// block that denies consumes none, so the ticks count commits rather than blocks.
    txn_tick: i64,
    /// The block in progress, while one is.
    txn: Option<TxnFrame>,
    /// Sources the harness supplied, by the name a zero-argument call names.
    sources: BTreeMap<String, Collection>,
    /// Mutable variables. Separate from the lexical scopes because a write inside a loop
    /// body outlives the iteration that made it, which a scope popped per iteration cannot.
    mut_vars: BTreeMap<String, Value>,
    /// User functions, by name: parameter names and body.
    functions: BTreeMap<String, (Vec<String>, Vec<Spanned<Stmt>>)>,
    site: FeedSite,
}

impl Interp {
    pub fn new(sources: BTreeMap<String, Collection>) -> Self {
        Self {
            scopes: vec![Vec::new()],
            sinks: BTreeMap::new(),
            sources,
            observed: std::collections::BTreeSet::new(),
            yielded: None,
            txn_tick: 0,
            txn: None,
            mut_vars: BTreeMap::new(),
            functions: BTreeMap::new(),
            site: FeedSite(Value::Unit),
        }
    }

    fn lookup(&self, name: &str) -> Option<&Value> {
        self.scopes
            .iter()
            .rev()
            .find_map(|s| s.iter().rev().find(|(n, _)| n == name).map(|(_, v)| v))
            .or_else(|| self.mut_vars.get(name))
    }

    fn bind(&mut self, name: impl Into<String>, value: Value) {
        self.scopes
            .last_mut()
            .expect("at least one scope")
            .push((name.into(), value));
    }

    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.scopes.push(Vec::new());
        let out = f(self);
        self.scopes.pop();
        out
    }
}

/// Run `source`, answering what each sink observed.
pub fn run(source: &str, sources: BTreeMap<String, Collection>) -> Result<Observations, Error> {
    let parsed = chl_parser::parse_module(source);
    let Some(module) = parsed.value else {
        return err(format!("parse error: {:?}", parsed.errors));
    };
    let mut interp = Interp::new(sources);
    interp.exec_block(&module.body)?;

    Ok(interp
        .sinks
        .iter()
        .filter(|(name, _)| interp.observed.contains(*name))
        .map(|(name, contributions)| (name.clone(), channel_value(contributions)))
        .collect())
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
                let name = match &target.node {
                    AssignTarget::Name(n) => n.to_string(),
                    other => return err(format!("unsupported assignment target: {other:?}")),
                };
                if is_zero_arg_call(&value.node, "test_sink") {
                    self.sinks.entry(name.clone()).or_default();
                    self.observed.insert(name);
                    return Ok(None);
                }
                if is_zero_arg_call(&value.node, "defer") {
                    self.sinks.entry(name).or_default();
                    return Ok(None);
                }
                let v = self.eval(value)?;
                self.bind(name, v);
                Ok(None)
            }

            // The annotation states a type; nothing here reads types.
            Stmt::AnnAssign { target, value, .. } => {
                let name = name_of(target)?;
                let v = self.eval(value)?;
                self.bind(name, v);
                Ok(None)
            }

            // `x := e` both declares a mutable variable and writes it, and `m[k] := e`
            // writes one entry of one. Inside a block the write is immediately visible to
            // later reads in the same block, which is what read-your-writes means, and it
            // is what decides the block commits.
            Stmt::MutAssign { target, value, .. } => {
                let v = self.eval(value)?;
                match &target.node {
                    AssignTarget::Name(n) => {
                        self.mut_vars.insert(n.to_string(), v);
                    }
                    AssignTarget::Subscript { target, index } => {
                        let Expr::Name(n) = &target.node else {
                            return err("a keyed write names a mutable variable");
                        };
                        let key = self.eval(index)?;
                        let name = n.to_string();
                        let Some(Value::Collection(c)) = self.mut_vars.get(&name) else {
                            return err(format!("`{name}` is not a mutable collection"));
                        };
                        // Last write wins per key, and a key not yet present is added.
                        let mut entries: Vec<(Value, Value)> = c
                            .entries()
                            .iter()
                            .filter(|(k, _)| *k != key)
                            .cloned()
                            .collect();
                        entries.push((key, v));
                        self.mut_vars
                            .insert(name, Value::Collection(Collection::from_entries(entries)));
                    }
                    other => return err(format!("unsupported write target: {other:?}")),
                }
                if let Some(frame) = self.txn.as_mut() {
                    frame.wrote = true;
                }
                Ok(None)
            }

            Stmt::AugAssign { target, op, value } => {
                let name = name_of(target)?;
                let current = self
                    .lookup(&name)
                    .cloned()
                    .ok_or_else(|| Error(format!("unbound name: {name}")))?;
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
                match self.mut_vars.entry(name.clone()) {
                    std::collections::btree_map::Entry::Occupied(mut slot) => {
                        slot.insert(updated);
                    }
                    std::collections::btree_map::Entry::Vacant(_) => self.bind(name, updated),
                }
                Ok(None)
            }

            // `out <<= e` contributes once, like a feed that cannot repeat.
            Stmt::Define { target, value } => {
                let name = name_of(target)?;
                if self.sinks.contains_key(&name) {
                    let v = self.eval(value)?;
                    let key = self.site.0.clone();
                    let site = value.span.start;
                    self.sinks
                        .get_mut(&name)
                        .expect("checked")
                        .push((site, key, v));
                } else {
                    let v = self.eval(value)?;
                    self.bind(name, v);
                }
                Ok(None)
            }

            Stmt::If {
                branches,
                else_body,
            } => {
                for branch in branches {
                    let Value::Bool(taken) = self.eval(&branch.cond)? else {
                        return err("an `if` condition is a boolean");
                    };
                    if taken {
                        return self.exec_block(&branch.body);
                    }
                }
                match else_body {
                    Some(body) => self.exec_block(body),
                    None => Ok(None),
                }
            }

            // Tag dispatch: the first arm whose tag matches, or a wildcard arm.
            Stmt::Match { scrutinee, arms } => {
                let (bound, body) = self.match_arm(scrutinee, arms)?;
                let body = body.to_vec();
                self.scoped(|me| {
                    if let Some((n, v)) = bound {
                        me.bind(n, v);
                    }
                    me.exec_block(&body)
                })
            }

            Stmt::FunctionDef {
                name, params, body, ..
            } => {
                self.functions.insert(
                    name.to_string(),
                    (
                        params.iter().map(|p| p.name.to_string()).collect(),
                        body.clone(),
                    ),
                );
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
                let outer = self.site.clone();
                for (key, elem) in c.entries().to_vec() {
                    // The loop's key is the feed site's key: a contribution from inside
                    // this body lands under the position its element came from.
                    self.site = FeedSite(key);
                    let returned = self.scoped(|me| {
                        me.bind(name.clone(), elem);
                        me.exec_block(body)
                    })?;
                    if let Some(v) = returned {
                        self.site = outer;
                        return Ok(Some(v));
                    }
                }
                self.site = outer;
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
                    let key = self.site.0.clone();
                    let v = self.eval(inner)?;
                    self.yielded.as_mut().expect("checked").push((key, v));
                    return Ok(None);
                }
                self.eval(e).map(|_| None)
            }

            // `with begin():` — one commit record per block, at the next tick, or none if
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
                self.txn = Some(TxnFrame::default());
                let outcome = self.scoped(|me| me.exec_block(body));
                let frame = self.txn.take().expect("installed above");
                outcome?;

                if !frame.wrote && frame.replies.is_empty() {
                    // Denied: no write, no reply, no tick.
                    return Ok(None);
                }
                self.txn_tick += 1;
                let tick = Value::Int(self.txn_tick);
                for (channel, site, value) in frame.replies {
                    self.sinks
                        .get_mut(&channel)
                        .expect("a reply names an open channel")
                        .push((site, tick.clone(), value));
                }
                Ok(None)
            }

            Stmt::Pass => Ok(None),
            other => err(format!("unsupported statement: {other:?}")),
        }
    }

    fn feed(&mut self, target: &Spanned<Expr>, value: &Spanned<Expr>) -> Result<(), Error> {
        let Expr::Name(name) = &target.node else {
            return err("a feed's target is a name");
        };
        let name = name.to_string();
        if !self.sinks.contains_key(&name) {
            return err(format!("`{name}` is not a sink"));
        }
        let contributed = self.eval(value)?;
        // The feed's source position identifies the site: two `<<` in one program are two
        // places whatever they write.
        let site = value.span.start;
        if let Some(frame) = self.txn.as_mut() {
            // A reply rides its block's commit, so it is indexed by commit tick, not by
            // the iteration that produced it. The tick is not known until the block
            // commits, so the reply waits here.
            frame.replies.push((name, site, contributed));
            return Ok(());
        }
        let key = self.site.0.clone();
        self.sinks
            .get_mut(&name)
            .expect("checked above")
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

/// What a channel holds: its contributions keyed as the channel's domain keys them.
///
/// One feed site leaves the keys alone. Several make the channel a union of them, so each
/// key is tagged by the site's position among those that fed this channel.
fn channel_value(contributions: &[(usize, Value, Value)]) -> Value {
    let mut sites: Vec<usize> = Vec::new();
    for (site, _, _) in contributions {
        if !sites.contains(site) {
            sites.push(*site);
        }
    }
    let entries = contributions
        .iter()
        .map(|(site, key, value)| {
            let key = if sites.len() > 1 {
                let tag = sites
                    .iter()
                    .position(|s| s == site)
                    .expect("collected above");
                Value::Variant {
                    tag: tag.to_string(),
                    payload: Box::new(key.clone()),
                }
            } else {
                key.clone()
            };
            (key, value.clone())
        })
        .collect();
    Value::Collection(Collection::from_entries(entries))
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
                if let Some(contributions) = self.sinks.get(n.as_str()) {
                    return Ok(channel_value(contributions));
                }
                self.lookup(n)
                    .cloned()
                    .ok_or_else(|| Error(format!("unbound name: {n}")))
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
                    (UnaryOp::Neg, Value::Int(i)) => Ok(Value::Int(-i)),
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
                self.comprehend(&comp.clauses, &comp.element, &mut out)?;
                Ok(Value::Collection(Collection::from_entries(out)))
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
                            me.bind(n, v);
                        }
                        me.block_value(&body)
                    })
                }
                Stmt::If {
                    branches,
                    else_body,
                } => {
                    for branch in branches {
                        let Value::Bool(taken) = self.eval(&branch.cond)? else {
                            return err("an `if` condition is a boolean");
                        };
                        if taken {
                            let body = branch.body.clone();
                            return self.scoped(|me| me.block_value(&body));
                        }
                    }
                    match else_body {
                        Some(body) => {
                            let body = body.clone();
                            self.scoped(|me| me.block_value(&body))
                        }
                        None => err("an `if` with no `else` denotes no value"),
                    }
                }
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
        // A user function shadows nothing built in: the compiler rejects a redefinition.
        if let Some((params, body)) = self.functions.get(name.as_str()).cloned() {
            if params.len() != args.len() {
                return err(format!(
                    "`{name}` takes {} argument(s), given {}",
                    params.len(),
                    args.len()
                ));
            }
            let mut bound = Vec::with_capacity(args.len());
            for a in args {
                bound.push(self.eval(a)?);
            }
            let generator = contains_yield(&body);
            return self.scoped(|me| {
                for (p, v) in params.iter().zip(bound) {
                    me.bind(p.clone(), v);
                }
                if !generator {
                    return me.block_value(&body);
                }
                // A generator denotes the collection of what it yielded, keyed by the
                // position each value was drawn from.
                let outer = me.yielded.take();
                me.yielded = Some(Vec::new());
                let outcome = me.exec_block(&body);
                let collected = me.yielded.take().expect("installed above");
                me.yielded = outer;
                outcome?;
                Ok(Value::Collection(Collection::from_entries(collected)))
            });
        }

        match (name.as_str(), args.len()) {
            // Every commit has landed by the time the program's statements are done, so
            // the terminal read is the variable's value.
            ("await_final", 1) => {
                let Expr::Name(n) = &args[0].node else {
                    return err("`await_final` takes a mutable variable");
                };
                self.mut_vars
                    .get(n.as_str())
                    .cloned()
                    .ok_or_else(|| Error(format!("`{n}` is not a mutable variable")))
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
                Ok(Value::Collection(Collection::from_entries(entries)))
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
                    .ok_or_else(|| Error("`max` of an empty collection".into()))
            }

            (name, 0) => match self.sources.get(name) {
                Some(c) => Ok(Value::Collection(c.clone())),
                None => err(format!("unknown zero-argument function: {name}")),
            },

            ("sum", 1) => {
                let Value::Collection(c) = self.eval(&args[0])? else {
                    return err("`sum` takes a collection");
                };
                let mut total = 0i64;
                for (_, v) in c.entries() {
                    let Value::Int(i) = v else {
                        return err("`sum` takes a collection of integers");
                    };
                    total += i;
                }
                Ok(Value::Int(total))
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
                Ok(Value::Collection(Collection::from_entries(
                    groups
                        .into_iter()
                        .map(|(k, members)| {
                            (k, Value::Collection(Collection::from_entries(members)))
                        })
                        .collect(),
                )))
            }

            (name, n) => err(format!("unknown function `{name}` of {n} argument(s)")),
        }
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
            me.bind(name, arg);
            me.eval(body)
        })
    }

    /// Walk a comprehension's clauses, collecting `key -> element` for each surviving
    /// binding. The key is the position the element came from, so a filter keeps the
    /// positions of its survivors rather than renumbering them.
    fn comprehend(
        &mut self,
        clauses: &[CompClause],
        element: &Spanned<Expr>,
        out: &mut Vec<(Value, Value)>,
    ) -> Result<(), Error> {
        match clauses.split_first() {
            None => {
                let key = self.site.0.clone();
                let v = self.eval(element)?;
                out.push((key, v));
                Ok(())
            }
            Some((CompClause::If(guard), rest)) => {
                let Value::Bool(keep) = self.eval(guard)? else {
                    return err("a comprehension guard is a boolean");
                };
                if keep {
                    self.comprehend(rest, element, out)?;
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
                let outer = self.site.clone();
                for (key, elem) in c.entries().to_vec() {
                    self.site = FeedSite(key);
                    self.scoped(|me| {
                        me.bind(name.clone(), elem);
                        me.comprehend(rest, element, out)
                    })?;
                }
                self.site = outer;
                Ok(())
            }
        }
    }
}

fn binop(op: BinOp, l: Value, r: Value) -> Result<Value, Error> {
    match (op, &l, &r) {
        (BinOp::Add | BinOp::AddRefined, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
        (BinOp::Add, Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
        (BinOp::FloorDiv, Value::Int(_), Value::Int(0)) => err("division by zero"),
        (BinOp::FloorDiv, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.div_euclid(*b))),
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
            Ok(Value::Collection(Collection::from_entries(out)))
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
