//! Replacing a running program with a new version of its source, and running
//! several versions of it side by side as branches.
//!
//! A [`LiveProgram`] is the process's branch table: a named entry per branch,
//! each holding its version number, its branch provenance, its compiled version
//! and the operators that version runs
//! (`src/ccl/design/program-evolution.md`, "The branch table"). A reload swaps
//! one branch's version for its next; the new version inherits that branch's
//! sources and sinks and whichever of its operators compute the same thing, and
//! everything else is rebuilt. Branch-and-reload creates a branch by the same
//! reload taken against its parent's version, and delete removes one.
//!
//! # What a reload may change
//!
//! Its logic freely, and its sources and sinks by addition: a version may open a
//! source or a sink the running program does not have and serves it as soon as
//! the swap completes, and one it stops serving is retired. What it may not do is
//! break the continuity of state — see [`reload`](LiveProgram::reload).
//!
//! # What survives it
//!
//! Every `Let` binding, every `Transact` store and every iteration input whose
//! computation is unchanged, together with what that computation has
//! accumulated. The structural diff of the two versions' trees
//! ([`diff`](crate::ccl::diff::diff)) says which node of the new tree stands
//! where each node of the old one did, and conversion keeps the operator
//! recorded at a corresponding node rather than building a second one — so an
//! accumulator the reload did not touch keeps its accumulation, and a fold
//! partway through a collection keeps its place. Reuse is hereditary: an
//! operator is kept only when every binding it reads was kept too, so a
//! carried-forward operator is never left reading a subgraph the reload rebuilt.
//!
//! A variable keeps its value even where its logic was edited. Its store is
//! rebuilt, and each variable it still declares is seeded from what the retired
//! version left it holding, so the new rule governs from the swap onwards without
//! discarding what came before. Neither how much a reload reuses nor what it
//! carries depends on how many reloads preceded it: a kept binding hands on
//! everything recorded under it, which is what keeps a variable declared inside a
//! function body carried across a reload that rebuilt nothing around it.
//!
//! A binding compiled under an iteration is rebuilt regardless. Its operator is
//! parameterized by an iteration input that is not part of the term, so the term
//! does not identify it.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    fmt,
    rc::{Rc, Weak},
};

use crate::ccl::{
    Expr,
    context::{
        CompileError, CompiledProgram, GlobalContext, Phase, compile_program, compile_replacement,
    },
    diff::diff,
};
use crate::interpreter::{
    Consumer, Value,
    operator_conversion::{Inheritance, ReuseTally, StateConflict, UnreadablePrefix, VarPath},
    tile_operators::{FanOut, TileProducer},
};

/// The branch a request that names none addresses: a control-port verb without
/// a branch segment, the single-branch accessors, and the unlabelled output of
/// the binary's driver. The process starts with a branch of this name, and the
/// name means whichever branch holds it, so once that branch is deleted a
/// branch created under the name takes its place.
pub const DEFAULT_BRANCH: &str = "main";

/// Builds the consumer that wakes the driver for a program's `main` output.
///
/// Called once per version: each compilation subscribes its own.
pub type MainConsumerFactory<'a> = &'a dyn Fn() -> Box<dyn Consumer>;

/// Whether `name` is spelled as a branch name may be: a non-empty run of ASCII
/// letters, digits, `-` and `_`, which is what one path segment of the control
/// port carries.
pub fn is_branch_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
}

/// The `<parent>@<n>` a branch was created from.
///
/// Recorded once, at creation, and read by no reload, so it can name a version
/// its parent has since replaced or a branch since deleted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Provenance {
    pub parent: String,
    pub version: u64,
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@{}", self.parent, self.version)
    }
}

/// One branch's entry: its branch provenance, its version number, its version,
/// and the operators it holds.
struct Branch {
    name: String,
    /// `None` for the root, which was not created by branch-and-reload.
    provenance: Option<Provenance>,
    /// The current version's number.
    version: u64,
    /// Every version this entry has installed, from the one it was created at,
    /// with the tally of the reload that installed it.
    history: Vec<(u64, ReuseTally)>,
    /// The current version. Its source is the only one the entry keeps.
    program: CompiledProgram,
    /// The `main` output's producer, held out of `program.outputs` so the other
    /// outputs stay borrowable while the driver pulls it. `None` for a sink
    /// program and for a torn-down version.
    main_producer: Option<Box<dyn TileProducer>>,
    /// Set by the `main` output's consumer and by an install, cleared by the
    /// pull that answers it.
    main_notified: Rc<Cell<bool>>,
    /// Whether the `main` output has released everything, after which the
    /// driver stops pulling it.
    main_finished: bool,
    /// Whether every sink output has reached a terminal tile. Latched, because
    /// [`CompiledProgram::done`] fires once.
    sinks_done: bool,
    /// The operators this branch holds, by the node of its version's tree each
    /// was built from. An operator lives as long as some entry's record holds
    /// it.
    record: Inheritance,
}

impl Branch {
    /// Every producer registered with a data source that this branch holds:
    /// the ones its current version's compilation registered, and the ones under
    /// the operators its record holds. What a source's start for a replacement's
    /// new producers is taken from (`src/ccl/design/program-evolution.md`,
    /// "Routes across branches").
    fn source_readers(&self) -> HashSet<String> {
        let mut readers = self.record.source_readers();
        readers.extend(self.program.source_readers.iter().cloned());
        readers
    }

    /// Drop this version's subscriptions, keeping the tree it was built from.
    ///
    /// Detaching the sinks is what ends this version's dispatch, and dropping
    /// the outputs alone does not achieve it: an operator the next version
    /// carries forward still holds the notification closure that reaches this
    /// version's sink consumers, so they would keep being woken and keep writing
    /// to sinks the next version now owns
    /// ([`SinkConsumer::detach`](crate::interpreter::SinkConsumer::detach)).
    ///
    /// Every sink consumer is detached. The ownership rule is that a branch
    /// detaches only the sink consumers no other entry holds, and a sink
    /// consumer is built by the compilation of one version, which one entry
    /// holds: branch-and-reload builds the new branch's own rather than sharing
    /// its parent's (`src/ccl/design/program-evolution.md`, "A branch is created
    /// by branch-and-reload").
    ///
    /// The tree stays because the reload diffs against it and the compile of
    /// the replacement keys reuse on it.
    fn tear_down(&mut self) {
        self.main_producer = None;
        for output in &self.program.outputs {
            if let Some(consumer) = &output.sink_consumer {
                consumer.borrow_mut().detach();
            }
        }
        self.program.outputs.clear();
    }

    /// Install `program` as this entry's version `version`, holding `record`.
    fn install(&mut self, program: CompiledProgram, record: Inheritance, reuse: ReuseTally) {
        let (program, main_producer) = driving(program);
        self.program = program;
        self.main_producer = main_producer;
        self.record = record;
        self.version += 1;
        self.history.push((self.version, reuse));
        self.main_finished = false;
        self.sinks_done = false;
        // The new graph has subscribed and nothing has pulled it yet.
        self.main_notified.set(true);
    }
}

/// Move `program`'s `main` producer out of its outputs, so the driver can pull
/// it while the other outputs stay borrowable.
fn driving(mut program: CompiledProgram) -> (CompiledProgram, Option<Box<dyn TileProducer>>) {
    let main_producer = program.main_mut().and_then(|o| o.producer.take());
    (program, main_producer)
}

/// The consumer a branch's `main` output is subscribed with: it marks the
/// branch as having something to pull, then wakes the driver.
fn branch_main_consumer(
    notified: &Rc<Cell<bool>>,
    main_consumer: MainConsumerFactory<'_>,
) -> Box<dyn Consumer> {
    let notified = notified.clone();
    let mut wake = main_consumer();
    Box::new(move || {
        notified.set(true);
        wake.notify();
    })
}

/// One row of [`LiveProgram::branches`], rendered as `/branches/list` prints it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchSummary {
    pub name: String,
    /// The current version number.
    pub version: u64,
    /// The branch provenance: `None` for the root.
    pub provenance: Option<Provenance>,
    /// How many distinct fan-outs the entry's record holds, sink consumers not
    /// counted.
    pub operators: usize,
    /// How many of those some other entry also holds.
    pub shared: usize,
}

impl fmt::Display for BranchSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let from = self
            .provenance
            .as_ref()
            .map_or_else(|| "-".to_string(), Provenance::to_string);
        write!(
            f,
            "{}\tversion={}\tfrom={from}\toperators={}\tshared={}",
            self.name, self.version, self.operators, self.shared,
        )
    }
}

/// Why a branch operation did nothing.
#[derive(Debug)]
pub enum BranchError {
    /// The table holds no branch of that name. The control port answers 404.
    Unknown(String),
    /// The operation is refused, and the string says why. The control port
    /// answers 400.
    Refused(String),
    /// The version does not compile, or cannot take over the state its
    /// predecessor holds. The control port answers 400.
    Compile(Vec<CompileError>),
}

impl fmt::Display for BranchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BranchError::Unknown(name) => write!(f, "no branch named `{name}`"),
            BranchError::Refused(why) => f.write_str(why),
            BranchError::Compile(errs) => write!(f, "{} compile error(s)", errs.len()),
        }
    }
}

impl From<Vec<CompileError>> for BranchError {
    fn from(errs: Vec<CompileError>) -> Self {
        BranchError::Compile(errs)
    }
}

/// The process's branch table, and the verbs that change what runs.
///
/// Every branch runs from the moment it is created. The table is never empty:
/// the root is created with the process, and the last branch cannot be deleted.
pub struct LiveProgram {
    /// Every branch the table holds, in creation order.
    branches: Vec<Branch>,
    /// The last version number of every deleted name the table does not hold
    /// again. A branch created under that name continues from it.
    tombstones: HashMap<String, u64>,
}

/// What one accepted reload did.
pub struct ReloadReport {
    /// The rendered difference between the two versions, and nothing else: the
    /// report below is a second answer about the same pair, not part of it.
    pub diff: String,
    /// How much of the replaced version's graph the new one kept.
    pub reuse: ReuseTally,
    /// The loops this version adds that begin above the beginning of what they
    /// read. Empty for a reload that adds no loop over a consumed input, which
    /// is every reload of a program whose collections are built rather than
    /// read.
    pub unreadable: Vec<UnreadablePrefix>,
}

/// What one accepted [`LiveProgram::create_branch`] did.
pub struct Created {
    /// The new branch's name and first version number.
    pub name: String,
    pub version: u64,
    /// The branch provenance it was created with.
    pub from: Provenance,
    /// The creating reload's report.
    pub report: ReloadReport,
}

/// What one [`LiveProgram::diff_against`] question answered.
///
/// The two answers a [`ReloadReport`] carries, minus what only a reload can say,
/// so `/diff` and `/reload` render alike and an author reads the report before
/// the swap in the shape it will have after it.
pub struct DiffReport {
    /// The rendered difference between the two versions.
    pub diff: String,
    /// The loops the new version adds that would begin above the beginning of
    /// what they read.
    pub unreadable: Vec<UnreadablePrefix>,
}

/// What a difference reads as where there is none.
fn no_difference(phase: Phase) -> String {
    format!("no difference at phase {phase:?}\n")
}

/// The loops that begin above the beginning of their input, one per line, and
/// the empty string for none.
///
/// One renderer for both replies, so the note reads the same whether `/diff`
/// raised it before a swap or `/reload` reported it after. It ends a reply
/// rather than opening one: what changed is the answer, and this is the caveat
/// on it.
pub fn render_unreadable(unreadable: &[UnreadablePrefix]) -> String {
    unreadable.iter().map(|u| format!("\n{u}")).collect()
}

/// How `code` differs from `previous` at `phase`, or `None` where the two are
/// identical.
///
/// The difference alone. What a reload additionally reports rides its
/// [`ReloadReport`] rather than this string, so that a reply carrying both
/// neither says the report twice nor compiles the planned tree twice to derive
/// it.
///
/// Compiles both sides against the running sources and sinks, which opens
/// nothing and leaves every branch untouched: a route the registry does not
/// hold is named rather than opened
/// ([`Endpoints::Inherited`](crate::ccl::lower::Endpoints::Inherited)).
fn difference(
    ctx: &GlobalContext,
    previous: &str,
    code: &str,
    phase: Phase,
) -> Result<Option<String>, Vec<CompileError>> {
    let old = ctx.sources_and_sinks().compile_to(previous, phase)?;
    let new = ctx.sources_and_sinks().compile_to(code, phase)?;
    let d = diff(&old, &new);
    if d.is_identical() {
        return Ok(None);
    }
    Ok(Some(format!(
        "phase {phase:?}: {} divergence(s), {} shared root(s)\n\n{d}",
        d.divergences().len(),
        d.shared_roots().len(),
    )))
}

/// The refusal of a version that cannot take over the state its predecessor
/// holds, as one diagnostic.
fn state_refusal(conflicts: &[StateConflict]) -> CompileError {
    // Two failures, and they are opposite ways round: state the running
    // program holds that this version cannot take over, and state this
    // version asks for that no running program holds. They read as
    // separate paragraphs because the remedy for one says nothing about
    // the other.
    let (absent, unseatable): (Vec<&StateConflict>, Vec<&StateConflict>) =
        conflicts.iter().partition(|c| {
            matches!(
                c,
                StateConflict::NoPredecessor { .. } | StateConflict::Undecided { .. }
            )
        });
    // A swap reports both of its directions, and they render the same.
    let render = |group: &[&StateConflict]| {
        let mut lines: Vec<String> = group.iter().map(|c| c.to_string()).collect();
        lines.sort();
        lines.dedup();
        lines.join(", ")
    };
    let mut paragraphs: Vec<String> = Vec::new();
    if !unseatable.is_empty() {
        // Naming the declarations is the fix for a positional clash, and
        // it is not one an author would guess from the other refusals.
        let remedy = if unseatable.iter().any(|c| {
            matches!(
                c,
                StateConflict::Moved { .. } | StateConflict::LoadFromAnonymous { .. }
            )
        }) {
            "\nBind each of those declarations to its own name — `a = f(…)` rather than a \
             bare `f(…)` — and a reload can follow them wherever they move, and a \
             `@LoadFrom` can say which one it reads."
        } else if unseatable
            .iter()
            .any(|c| matches!(c, StateConflict::LoadFromAt { .. }))
        {
            // The declaration's annotation is what the value is read
            // at, so it has to state the whole of what the running
            // program holds rather than the part this version uses.
            "\nThe annotation on a `@LoadFrom` declaration is the shape the value is read at, so \
             it has to state the whole of what the running program holds."
        } else {
            ""
        };
        paragraphs.push(format!(
            "this version cannot take over state the running program is holding: {}. \
A value carries forward into the same variable at the same type, or into what a `@LoadFrom` reads \
it into, and only where the source says which variable it belongs to.\n\
Nothing else is refused: logic may change freely, endpoints may come and go, and a variable \
may move between loops.{remedy}",
            render(&unseatable),
        ));
    }
    if !absent.is_empty() {
        // The two have different remedies: a name nothing declares is a
        // source to fix, while a name declared but undecided is a value
        // the running program has not produced, which no edit to this
        // version reaches.
        // Each remedy that applies is rendered: picking one leaves the other's
        // names carrying advice that does not answer for them.
        let mut remedy = String::new();
        if absent
            .iter()
            .any(|c| matches!(c, StateConflict::NoPredecessor { .. }))
        {
            remedy.push_str(
                "\nA source containing `@LoadFrom` is an upgrade of a specific \
                 predecessor; with the migration taken out it starts from nothing \
                 like any other.",
            );
        }
        if absent
            .iter()
            .any(|c| matches!(c, StateConflict::Undecided { .. }))
        {
            remedy.push_str(
                "\nA store nothing reads is never driven, so it decides no value to \
                 hand on. Reading the variable somewhere in the running program is \
                 what gives it one.",
            );
        }
        paragraphs.push(format!(
            "this version reads state the running program does not hold: {}.{remedy}",
            render(&absent),
        ));
    }
    CompileError::Unsupported(paragraphs.join("\n\n"))
}

/// What a reload checks before anything is torn down, and what it reports.
struct Checked {
    diff: String,
    unreadable: Vec<UnreadablePrefix>,
}

impl LiveProgram {
    /// Compile `code` and subscribe it as the root, `main@1`.
    pub fn start(
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        let main_notified = Rc::new(Cell::new(false));
        let program = compile_program(
            ctx,
            code,
            branch_main_consumer(&main_notified, main_consumer),
        )?;
        let (program, main_producer) = driving(program);
        let root = Branch {
            name: DEFAULT_BRANCH.to_string(),
            provenance: None,
            version: 1,
            // A first compilation keeps nothing, so its tally is `0` kept of
            // everything it bound.
            history: vec![(1, ctx.reuse())],
            program,
            main_producer,
            main_notified,
            main_finished: false,
            sinks_done: false,
            record: ctx.take_record(),
        };
        Ok(LiveProgram {
            branches: vec![root],
            tombstones: HashMap::new(),
        })
    }

    /// The index of the branch named `name`.
    fn index_of(&self, name: &str) -> Result<usize, BranchError> {
        self.branches
            .iter()
            .position(|b| b.name == name)
            .ok_or_else(|| BranchError::Unknown(name.to_string()))
    }

    /// The branch the single-branch accessors answer for: the one named
    /// [`DEFAULT_BRANCH`]. While no branch holds that name they answer `None`
    /// rather than pick another branch, the way a control verb without a branch
    /// segment answers 404 (`src/ccl/design/program-evolution.md`, "The control
    /// port").
    fn default_branch(&self) -> Option<&Branch> {
        self.branches.iter().find(|b| b.name == DEFAULT_BRANCH)
    }

    /// The compiled program `main` runs, while the table holds `main`.
    pub fn program(&self) -> Option<&CompiledProgram> {
        self.default_branch().map(|b| &b.program)
    }

    /// The compiled program branch `name` runs.
    pub fn branch_program(&self, name: &str) -> Option<&CompiledProgram> {
        let at = self.index_of(name).ok()?;
        Some(&self.branches[at].program)
    }

    /// `main`'s `main` output's producer, for inspection.
    pub fn main_producer(&self) -> Option<&dyn TileProducer> {
        self.default_branch()?.main_producer.as_deref()
    }

    /// `main`'s `main` output's producer, for a driver to pull.
    pub fn main_producer_mut(&mut self) -> Option<&mut Box<dyn TileProducer>> {
        self.branch_main_producer_mut(DEFAULT_BRANCH)
    }

    /// Branch `name`'s `main` output's producer, for a driver to pull.
    pub fn branch_main_producer_mut(&mut self, name: &str) -> Option<&mut Box<dyn TileProducer>> {
        let at = self.index_of(name).ok()?;
        self.branches[at].main_producer.as_mut()
    }

    /// The source `main`'s current version was compiled from, while the table
    /// holds `main`.
    pub fn source(&self) -> Option<&str> {
        self.default_branch().map(|b| b.program.source.as_str())
    }

    /// Pull every branch's `main` output that has something new, in creation
    /// order.
    ///
    /// `pull` is handed the branch's name and the producer, and answers whether that output has now finished. A finished
    /// output is not pulled again (`src/ccl/design/program-evolution.md`, "A
    /// reload changes no other branch"). Returns whether anything was pulled.
    pub fn pull_mains(
        &mut self,
        mut pull: impl FnMut(&str, &mut dyn TileProducer) -> bool,
    ) -> bool {
        let mut pulled = false;
        for branch in &mut self.branches {
            if branch.main_finished || !branch.main_notified.get() {
                continue;
            }
            let Some(producer) = branch.main_producer.as_mut() else {
                continue;
            };
            branch.main_notified.set(false);
            pulled = true;
            if pull(&branch.name, producer.as_mut()) {
                branch.main_finished = true;
            }
        }
        pulled
    }

    /// Whether some branch has a `main` output it has not finished.
    pub fn any_main_running(&self) -> bool {
        self.branches
            .iter()
            .any(|b| b.main_producer.is_some() && !b.main_finished)
    }

    /// Whether every branch has finished: its `main` output, where it has one,
    /// and every sink output, where it has any. The process exits then.
    pub fn finished(&mut self) -> bool {
        let mut all = true;
        for branch in &mut self.branches {
            let has_sinks = branch.program.sinks().next().is_some();
            if has_sinks && !branch.sinks_done && branch.program.done.try_recv().is_ok() {
                branch.sinks_done = true;
            }
            let main_done = branch.main_producer.is_none() || branch.main_finished;
            all &= main_done && (!has_sinks || branch.sinks_done);
        }
        all
    }

    /// Every branch, in creation order.
    pub fn branches(&self) -> Vec<BranchSummary> {
        let held: Vec<Vec<Rc<FanOut>>> =
            self.branches.iter().map(|b| b.record.operators()).collect();
        self.branches
            .iter()
            .enumerate()
            .map(|(at, b)| {
                let shared = held[at]
                    .iter()
                    .filter(|fan| {
                        held.iter().enumerate().any(|(other, ops)| {
                            other != at && ops.iter().any(|o| Rc::ptr_eq(o, fan))
                        })
                    })
                    .count();
                BranchSummary {
                    name: b.name.clone(),
                    version: b.version,
                    provenance: b.provenance.clone(),
                    operators: held[at].len(),
                    shared,
                }
            })
            .collect()
    }

    /// `/branches/list`'s reply: one line per branch, fields separated by a tab.
    pub fn render_branches(&self) -> String {
        self.branches().iter().map(|b| format!("{b}\n")).collect()
    }

    /// `/branch/<name>/info`'s reply: the branch's `/branches/list` line, a
    /// blank line, one line per version of the entry with the tally of the
    /// reload that installed it, a blank line, and the current version's source.
    pub fn render_info(&self, name: &str) -> Result<String, BranchError> {
        let at = self.index_of(name)?;
        let summary = &self.branches()[at];
        let branch = &self.branches[at];
        let versions: String = branch
            .history
            .iter()
            .map(|(n, ReuseTally { kept, bound })| format!("{n}\tkept={kept}/{bound}\n"))
            .collect();
        Ok(format!(
            "{summary}\n\n{versions}\n{}",
            branch.program.source
        ))
    }

    /// A weak handle on every operator branch `name`'s entry holds.
    ///
    /// Weak so that asking keeps nothing alive: a handle that no longer upgrades
    /// is an operator no entry holds, which has been freed.
    pub fn held_operators(&self, name: &str) -> Option<Vec<Weak<FanOut>>> {
        let at = self.index_of(name).ok()?;
        Some(
            self.branches[at]
                .record
                .operators()
                .iter()
                .map(Rc::downgrade)
                .collect(),
        )
    }

    /// The value each of branch `name`'s mutable variables holds, read off the
    /// stores its entry holds.
    pub fn held_state(&self, name: &str) -> Option<HashMap<VarPath, Value>> {
        let at = self.index_of(name).ok()?;
        Some(self.branches[at].record.live_state())
    }

    /// Answer what `/diff` asks of `main`.
    pub fn diff_against(
        &self,
        ctx: &GlobalContext,
        code: &str,
        phase: Phase,
    ) -> Result<DiffReport, Vec<CompileError>> {
        self.diff_branch(ctx, DEFAULT_BRANCH, code, phase)
            .map_err(|e| match e {
                BranchError::Compile(errs) => errs,
                other => vec![CompileError::Unsupported(other.to_string())],
            })
    }

    /// Answer what `/diff/<branch>` asks: how `code` differs from branch
    /// `name`'s current version at `phase`, which is what its reload diffs
    /// against, and what reloading it would report. Changes nothing.
    pub fn diff_branch(
        &self,
        ctx: &GlobalContext,
        name: &str,
        code: &str,
        phase: Phase,
    ) -> Result<DiffReport, BranchError> {
        let branch = &self.branches[self.index_of(name)?];
        // A version identical to the running one declares the same variables, so
        // none of them is new and the report is empty without being asked.
        let Some(diff) = difference(ctx, &branch.program.source, code, phase)? else {
            return Ok(DiffReport {
                diff: no_difference(phase),
                unreadable: Vec::new(),
            });
        };
        // A reload reports off the planned tree it is about to build. A question
        // has no such tree, so it compiles one — at `Phase::Planning` whatever
        // phase the difference was asked at, and without opening ports, which is
        // what separates asking from doing.
        let planned = ctx.sources_and_sinks().compile_to(code, Phase::Planning)?;
        Ok(DiffReport {
            diff,
            unreadable: ctx.unreadable_inputs(&branch.record, &branch.program.ast, &planned),
        })
    }

    /// Answer what `/diff/<a>/<b>` asks: how branch `b`'s current version
    /// differs from branch `a`'s at `phase`. Changes nothing.
    ///
    /// The difference alone: the report of loops that begin above their input
    /// belongs to a reload, and no reload takes one branch's version to the
    /// other's.
    pub fn diff_between(
        &self,
        ctx: &GlobalContext,
        a: &str,
        b: &str,
        phase: Phase,
    ) -> Result<String, BranchError> {
        let from = &self.branches[self.index_of(a)?].program.source;
        let to = &self.branches[self.index_of(b)?].program.source;
        Ok(difference(ctx, from, to, phase)?.unwrap_or_else(|| no_difference(phase)))
    }

    /// Replace `main`'s version with the one `code` describes. See
    /// [`reload_branch`](Self::reload_branch).
    pub fn reload(
        &mut self,
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, Vec<CompileError>> {
        self.reload_branch(ctx, DEFAULT_BRANCH, code, main_consumer)
            .map_err(|e| match e {
                BranchError::Compile(errs) => errs,
                other => vec![CompileError::Unsupported(other.to_string())],
            })
    }

    /// Everything a reload does before it tears anything down: the difference,
    /// the compile to [`Phase::Planning`] that binds the ports the new version
    /// adds, the state-takeover guard against `predecessor`, and the report of
    /// loops that begin above their input.
    ///
    /// On `Err` every branch is untouched and still serving, and the ports the
    /// compile bound are handed back.
    fn check(
        ctx: &mut GlobalContext,
        previous_source: &str,
        previous_ast: &Expr,
        predecessor: &Inheritance,
        code: &str,
    ) -> Result<Checked, Vec<CompileError>> {
        let diff = difference(ctx, previous_source, code, Phase::AsOfRead)?
            .unwrap_or_else(|| no_difference(Phase::AsOfRead));
        // This compile binds the ports the new version adds and keeps the
        // listeners, because binding is the one step it and the compile that
        // installs the version would otherwise not share: a port already in use
        // would fail only after the running graph was torn down. Refusing below
        // hands the ports back.
        let planned = ctx
            .sources_and_sinks_mut()
            .compile_to_opening(code, Phase::Planning)
            .inspect_err(|_| ctx.sources_and_sinks_mut().release_unrouted_ports())?;
        // What the new version can take over is read off its planned tree,
        // before anything is built from it, so a version that would lose a value
        // or change its type is refused while every branch is whole.
        let conflicts = ctx.state_conflicts(predecessor, &planned);
        if !conflicts.is_empty() {
            ctx.sources_and_sinks_mut().release_unrouted_ports();
            return Err(vec![state_refusal(&conflicts)]);
        }
        // Read before teardown, off the same planned tree the guard used, so this
        // and `/diff` answer alike and neither has to walk a graph that is gone.
        let unreadable = ctx.unreadable_inputs(predecessor, previous_ast, &planned);
        Ok(Checked { diff, unreadable })
    }

    /// The union of the routes every branch's version binds, the one at
    /// `except` left out.
    fn routes_bound_except(&self, except: Option<usize>) -> HashSet<String> {
        self.branches
            .iter()
            .enumerate()
            .filter(|(at, _)| Some(*at) != except)
            .flat_map(|(_, b)| b.program.routes.iter().cloned())
            .collect()
    }

    /// Replace branch `name`'s version with the one `code` describes, as
    /// version `n + 1` of that branch.
    ///
    /// The new version is diffed against the branch's own running version, the
    /// state guard runs against the branch's own variables, and the compile is
    /// offered the branch's own entry (`src/ccl/design/program-evolution.md`,
    /// "A reload diffs against the branch's own version"). No other entry
    /// changes: an operator this branch drops that another entry holds stays
    /// alive and running.
    ///
    /// Rejected when the new version cannot **take over the state**: every
    /// mutable variable the branch holds a value for must be one the new version
    /// still declares or loads, at the same type, so that its value is seeded
    /// rather than discarded. Those are the refusals [`StateConflict`] names.
    /// Everything else is allowed: logic freely, sources and sinks by addition,
    /// and a variable moving to another loop, which seeds with the value it held
    /// and counts positions in whatever it now iterates.
    ///
    /// On `Err` every branch is untouched and still serving: both the compile to
    /// [`Phase::Planning`] and the guard run before anything is torn down. That
    /// compile binds the ports the new version adds, so an address it cannot
    /// bind is one of the errors raised here rather than a failure of the
    /// compile that installs the version, which runs after the teardown and has
    /// nothing to reject to. A refusal hands those ports back.
    ///
    /// The guard's tree is compiled separately from the one that gets built.
    /// `run_frontend` goes from source to a stop phase and nothing continues a
    /// stopped tree into operator conversion, so checking before tearing down
    /// means compiling twice — see `src/ccl/design/program-evolution.md`,
    /// "Order of a reload".
    ///
    /// # Panics
    ///
    /// Panics if the real compile fails after the [`Phase::Planning`] one
    /// succeeded. The two run the same passes over the same sources and sinks,
    /// and the `Planning` one has already taken every port the version needs, so
    /// disagreement is a compiler bug, and one that has already torn the branch
    /// down, which is not a state to hand back to a caller as a rejection.
    pub fn reload_branch(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, BranchError> {
        let at = self.index_of(name)?;
        let checked = {
            let branch = &self.branches[at];
            Self::check(
                ctx,
                &branch.program.source,
                &branch.program.ast,
                &branch.record,
                code,
            )?
        };

        // Where this branch's producers stopped, read while they all exist:
        // tearing the graph down drops its outputs' producers, and a record dies
        // with its producer.
        ctx.carry_release_from(&self.branches[at].source_readers());
        let bound_elsewhere = self.routes_bound_except(Some(at));
        let branch = &mut self.branches[at];
        branch.tear_down();
        // The offer holds the branch's operators until conversion is over, as a
        // single program's reload always has; the entry takes the new record
        // once the compile is done.
        let previous_record = std::mem::take(&mut branch.record);
        ctx.offer_predecessor(&previous_record);
        drop(previous_record);
        // The tree the torn-down graph was built from is still here — a teardown
        // drops the producers, not the program — so the compile below can be
        // told which of its nodes the offer already has an operator for.
        let program = compile_replacement(
            ctx,
            code,
            branch_main_consumer(&branch.main_notified, main_consumer),
            &branch.program.ast,
            &bound_elsewhere,
        )
        .expect("a version that compiled to Planning must compile to operators");
        let reuse = ctx.reuse();
        branch.install(program, ctx.take_record(), reuse);
        Ok(ReloadReport {
            diff: checked.diff,
            reuse,
            unreadable: checked.unreadable,
        })
    }

    /// Create branch `name` from branch `parent`'s current version and reload
    /// it with `code`, as one step (`src/ccl/design/program-evolution.md`, "A
    /// branch is created by branch-and-reload").
    ///
    /// The reload takes the parent's version as its predecessor: the difference,
    /// the state guard and the correspondence are all taken against the parent,
    /// and the compile is offered the parent's entry by reference, which is read
    /// and left as it was. Each operator the new version keeps is the parent's,
    /// subscribed through one more fan-out slot, and each store it rebuilds is
    /// seeded from the value the parent's variable holds now. The new version
    /// builds its own sink consumers, so nothing of the parent's is torn down.
    ///
    /// The copy of the parent's entry the doc describes is never materialized:
    /// until its reload a copy computes and sends exactly what its parent does,
    /// so building the reload straight off the parent's entry is the same step
    /// with nothing to undo on a refusal.
    ///
    /// Refused when `name` is not a branch name or is already in the table, and
    /// for everything a reload refuses; `Unknown` for a parent the table does
    /// not hold. A refusal leaves no entry and every branch serving.
    ///
    /// # Panics
    ///
    /// As [`reload_branch`](Self::reload_branch).
    pub fn create_branch(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
        parent: &str,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Created, BranchError> {
        if !is_branch_name(name) {
            return Err(BranchError::Refused(format!(
                "`{name}` is not a branch name: use ASCII letters, digits, `-` and `_`\n"
            )));
        }
        if self.index_of(name).is_ok() {
            return Err(BranchError::Refused(format!(
                "branch `{name}` already exists\n"
            )));
        }
        let from = self.index_of(parent)?;
        let checked = {
            let p = &self.branches[from];
            Self::check(ctx, &p.program.source, &p.program.ast, &p.record, code)?
        };

        let bound_elsewhere = self.routes_bound_except(None);
        let p = &self.branches[from];
        ctx.carry_release_from(&p.source_readers());
        ctx.offer_predecessor(&p.record);
        let main_notified = Rc::new(Cell::new(false));
        let program = compile_replacement(
            ctx,
            code,
            branch_main_consumer(&main_notified, main_consumer),
            &p.program.ast,
            &bound_elsewhere,
        )
        .expect("a version that compiled to Planning must compile to operators");
        let reuse = ctx.reuse();
        let provenance = Provenance {
            parent: p.name.clone(),
            version: p.version,
        };
        let version = self.tombstones.remove(name).unwrap_or(0) + 1;
        let (program, main_producer) = driving(program);
        main_notified.set(true);
        self.branches.push(Branch {
            name: name.to_string(),
            provenance: Some(provenance.clone()),
            version,
            history: vec![(version, reuse)],
            program,
            main_producer,
            main_notified,
            main_finished: false,
            sinks_done: false,
            record: ctx.take_record(),
        });
        Ok(Created {
            name: name.to_string(),
            version,
            from: provenance,
            report: ReloadReport {
                diff: checked.diff,
                reuse,
                unreadable: checked.unreadable,
            },
        })
    }

    /// Delete branch `name`'s entry and leave its tombstone
    /// (`src/ccl/design/program-evolution.md`, "Deleting a branch").
    ///
    /// Its sink consumers are detached and its outputs dropped, and its
    /// operators are freed where no other entry holds them; a freed producer's
    /// `Drop` returns its release record to the source it read. Every route no
    /// remaining branch binds is retired. The branches created from it keep
    /// running what they hold, and their branch provenance still names it.
    ///
    /// Refused for the last branch in the table; `Unknown` for a name the table
    /// does not hold. Returns the version number the tombstone keeps.
    pub fn delete_branch(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
    ) -> Result<u64, BranchError> {
        let at = self.index_of(name)?;
        if self.branches.len() == 1 {
            return Err(BranchError::Refused(format!(
                "`{name}` is the last branch in the table and cannot be deleted\n"
            )));
        }
        let mut removed = self.branches.remove(at);
        removed.tear_down();
        let version = removed.version;
        drop(removed);
        self.tombstones.insert(name.to_string(), version);
        let still_bound = self.routes_bound_except(None);
        ctx.retire_routes_absent_from(&still_bound);
        Ok(version)
    }
}
