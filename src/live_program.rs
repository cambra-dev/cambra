//! Replacing a running program with a new version of its source, and running
//! several versions of it side by side as branches.
//!
//! A [`LiveProgram`] is the process's branch table: a named entry per branch,
//! each holding a compiled version and the operators that version runs, and the
//! operations that change what runs. [`reload`](LiveProgram::reload) swaps the
//! root branch, `production`, for another version, which is the hot reload a
//! single program has; the branch verbs create, reload, retarget and delete the
//! others (`src/ccl/design/program-evolution.md`, "The branch table").
//!
//! # What a reload may change
//!
//! Its logic freely, and its sources and sinks by addition: a version may open a
//! source or a sink the running program does not have and serves it as soon as
//! the swap completes, and one it stops serving is retired once no branch binds
//! it. What it may not do is break the continuity of state — see
//! [`reload`](LiveProgram::reload).
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
//!
//! # Branches
//!
//! A branch other than `production` is reloaded against its origin: the new
//! version is diffed against the origin's running version and offered the
//! origin's operators and state, and the origin's entry is read and left as it
//! was. An operator lives while some entry holds it, so one the origin drops
//! stays alive for as long as a branch still runs it.

use std::{
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
    sync::mpsc,
};

use crate::ccl::{
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

/// The root branch: the one the process starts with, and the one that has no
/// origin.
pub const ROOT: &str = "production";

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

/// One version of the program: a compiled program and the `main` output's
/// producer, which is what a single hot-reloaded program held before branches.
///
/// A version is shared by every branch whose entry names it, which is what a
/// branch created as a copy of its origin does until one of the two reloads.
/// Its sink consumers are shared with it, so they are detached only once no
/// entry names the version ([`LiveProgram::release_version`]).
struct Version {
    program: CompiledProgram,
    /// The `main` output's producer, held out of `program.outputs` so the other
    /// outputs stay borrowable while the driver pulls it. `None` for a sink
    /// program, for a torn-down version, and for one whose `main` a driver has
    /// pulled to its end.
    main_producer: Option<Box<dyn TileProducer>>,
}

impl Version {
    /// Hold `program`, with its `main` producer moved out of the outputs so the
    /// driver can pull it while the other outputs stay borrowable.
    fn driving(mut program: CompiledProgram) -> Self {
        let main_producer = program.main_mut().and_then(|o| o.producer.take());
        Version {
            program,
            main_producer,
        }
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
    /// The tree stays because a root reload diffs against it and the compile of
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
}

/// Which version a branch table entry runs, as a key into
/// [`LiveProgram::versions`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct VersionId(u64);

/// Where a branch was created from, or retargeted onto.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Origin {
    /// The root, which has none.
    Root,
    /// A branch the table holds.
    Running(String),
    /// A branch that has been deleted. The name is kept for `/branches/list`;
    /// it addresses nothing, including a later branch created under the same
    /// name.
    Deleted(String),
}

/// One branch's entry: its origin, its version, and the operators it holds.
struct Branch {
    name: String,
    origin: Origin,
    /// Set when the origin reloads or the branch is retargeted, and cleared by
    /// the branch's own reload.
    stale: bool,
    version: VersionId,
    /// The operators this branch holds, by the node of its version's tree each
    /// was built from, and the stores its variables live in. An operator lives
    /// as long as some entry's record holds it.
    record: Inheritance,
}

/// A branch's status, as `/branches/list` reports it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BranchStatus {
    /// Its version was compiled against its origin's current version, or it is
    /// the root.
    Current,
    /// Its origin has reloaded, or it has been retargeted, since it was created
    /// or last reloaded.
    Stale,
    /// Its origin has been deleted, so its reload is refused until it is
    /// retargeted.
    Orphaned,
}

impl std::fmt::Display for BranchStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            BranchStatus::Current => "current",
            BranchStatus::Stale => "stale",
            BranchStatus::Orphaned => "orphaned",
        })
    }
}

/// One row of [`LiveProgram::branches`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BranchSummary {
    pub name: String,
    /// The origin's name: `None` for the root, and the deleted origin's name for
    /// an orphan.
    pub origin: Option<String>,
    pub status: BranchStatus,
    /// How many operators the entry holds.
    pub operators: usize,
    /// How many of those some other entry also holds.
    pub shared: usize,
}

impl std::fmt::Display for BranchSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\t{}\t{}\toperators={}\tshared={}",
            self.name,
            self.origin.as_deref().unwrap_or("-"),
            self.status,
            self.operators,
            self.shared,
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

impl std::fmt::Display for BranchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
/// Every branch runs from the moment it is created. `production` is created with
/// the process and cannot be deleted, so every chain of origins no deletion has
/// broken ends at it.
pub struct LiveProgram {
    /// Every branch, `production` first and the rest in creation order.
    branches: Vec<Branch>,
    /// Every version some entry names. A version no entry names is torn down
    /// and dropped by [`collect_versions`](Self::collect_versions).
    versions: HashMap<VersionId, Version>,
    next_version: u64,
}

/// What one accepted [`LiveProgram::reload`] did.
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

impl LiveProgram {
    /// Compile `code` and subscribe it as `production`.
    pub fn start(
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<Self, Vec<CompileError>> {
        let program = compile_program(ctx, code, main_consumer())?;
        let mut live = LiveProgram {
            branches: Vec::new(),
            versions: HashMap::new(),
            next_version: 0,
        };
        let version = live.insert_version(Version::driving(program));
        live.branches.push(Branch {
            name: ROOT.to_string(),
            origin: Origin::Root,
            stale: false,
            version,
            record: ctx.take_record(),
        });
        Ok(live)
    }

    fn insert_version(&mut self, version: Version) -> VersionId {
        let id = VersionId(self.next_version);
        self.next_version += 1;
        self.versions.insert(id, version);
        id
    }

    fn root(&self) -> &Version {
        self.version_of(0)
    }

    fn version_of(&self, at: usize) -> &Version {
        &self.versions[&self.branches[at].version]
    }

    /// The index of the branch named `name`.
    fn index_of(&self, name: &str) -> Result<usize, BranchError> {
        self.branches
            .iter()
            .position(|b| b.name == name)
            .ok_or_else(|| BranchError::Unknown(name.to_string()))
    }

    /// The index of the branch a reload of the branch at `at` diffs against and
    /// is offered: its origin, or itself for the root. Refused for an orphan,
    /// which has no origin to diff against.
    fn predecessor_of(&self, at: usize) -> Result<usize, BranchError> {
        match &self.branches[at].origin {
            Origin::Root => Ok(at),
            Origin::Running(origin) => {
                let pred = self.index_of(origin);
                debug_assert!(
                    pred.is_ok(),
                    "a deleted origin is recorded as `Origin::Deleted`, so a running origin \
                     is in the table"
                );
                pred
            }
            Origin::Deleted(origin) => Err(BranchError::Refused(format!(
                "branch `{}` is orphaned: its origin `{origin}` was deleted, so there is no \
                 version to diff against. Retarget it first: /branch/{}/retarget/<origin>\n",
                self.branches[at].name, self.branches[at].name,
            ))),
        }
    }

    /// The compiled program `production` runs.
    pub fn program(&self) -> &CompiledProgram {
        &self.root().program
    }

    /// The compiled program branch `name` runs.
    pub fn branch_program(&self, name: &str) -> Option<&CompiledProgram> {
        let at = self.index_of(name).ok()?;
        Some(&self.version_of(at).program)
    }

    /// `production`'s `main` output's producer, for inspection.
    pub fn main_producer(&self) -> Option<&dyn TileProducer> {
        self.root().main_producer.as_deref()
    }

    /// `production`'s `main` output's producer, for a driver to pull.
    pub fn main_producer_mut(&mut self) -> Option<&mut Box<dyn TileProducer>> {
        self.branch_main_producer_mut(ROOT)
    }

    /// Branch `name`'s `main` output's producer, for a driver to pull. A branch
    /// sharing its origin's version shares its producer too, so the one
    /// operator graph is pulled once however many entries name it.
    pub fn branch_main_producer_mut(&mut self, name: &str) -> Option<&mut Box<dyn TileProducer>> {
        let at = self.index_of(name).ok()?;
        let id = self.branches[at].version;
        self.versions.get_mut(&id)?.main_producer.as_mut()
    }

    /// The `main` producer of every version `production` does not run, each
    /// labelled with the branches that run it, for a driver that pulls every
    /// running version. A slot is `None` once the driver has emptied it.
    ///
    /// A version is pulled for as long as some entry holds it, because a held
    /// fragment nothing pulls stops releasing and holds its inputs' agreement
    /// where it stopped (`src/ccl/design/program-evolution.md`, "An origin's
    /// reload leaves its branches stale").
    pub fn branch_mains_mut(&mut self) -> Vec<(String, &mut Option<Box<dyn TileProducer>>)> {
        let root = self.branches[0].version;
        let labels: HashMap<VersionId, String> = self
            .versions
            .keys()
            .map(|id| {
                let names: Vec<&str> = self
                    .branches
                    .iter()
                    .filter(|b| b.version == *id)
                    .map(|b| b.name.as_str())
                    .collect();
                (*id, names.join(","))
            })
            .collect();
        let mut out: Vec<(String, &mut Option<Box<dyn TileProducer>>)> = self
            .versions
            .iter_mut()
            .filter(|(id, v)| **id != root && v.main_producer.is_some())
            .map(|(id, v)| (labels[id].clone(), &mut v.main_producer))
            .collect();
        out.sort_by(|a, b| a.0.cmp(&b.0));
        out
    }

    /// Whether `production` has a `main` output to drive.
    pub fn has_main(&self) -> bool {
        self.root().main_producer.is_some()
    }

    /// Fires once every sink output of `production` has reached a terminal tile.
    pub fn done(&self) -> &mpsc::Receiver<()> {
        &self.root().program.done
    }

    /// The source `production` was compiled from.
    pub fn source(&self) -> &str {
        &self.root().program.source
    }

    /// Every branch, `production` first and the rest in creation order.
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
                let (origin, status) = match &b.origin {
                    Origin::Root => (None, BranchStatus::Current),
                    Origin::Running(o) if b.stale => (Some(o.clone()), BranchStatus::Stale),
                    Origin::Running(o) => (Some(o.clone()), BranchStatus::Current),
                    Origin::Deleted(o) => (Some(o.clone()), BranchStatus::Orphaned),
                };
                BranchSummary {
                    name: b.name.clone(),
                    origin,
                    status,
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

    /// Answer what `/diff` asks of `production`: how `code` differs from its
    /// running version at `phase`, and what reloading it would report.
    ///
    /// Compiles both sides against the running sources and sinks, which opens
    /// nothing and leaves the running program untouched: a route the registry does
    /// not hold is named rather than opened
    /// ([`Endpoints::Inherited`](crate::ccl::lower::Endpoints::Inherited)).
    /// Compiling the new version in a fresh [`GlobalContext`] instead would try to
    /// bind a port this program already holds.
    pub fn diff_against(
        &self,
        ctx: &GlobalContext,
        code: &str,
        phase: Phase,
    ) -> Result<DiffReport, Vec<CompileError>> {
        self.diff_branch(ctx, ROOT, code, phase)
            .map_err(|e| match e {
                BranchError::Compile(errs) => errs,
                other => unreachable!("the root has no origin to be orphaned from: {other}"),
            })
    }

    /// Answer what `/diff/<branch>` asks: how `code` differs from the version
    /// a reload of branch `name` would diff against, which is its origin's
    /// running version, or `production`'s own.
    ///
    /// Refused for an orphan, as its reload would be.
    pub fn diff_branch(
        &self,
        ctx: &GlobalContext,
        name: &str,
        code: &str,
        phase: Phase,
    ) -> Result<DiffReport, BranchError> {
        let at = self.index_of(name)?;
        let pred = self.predecessor_of(at)?;
        let previous = self.version_of(pred);
        // A version identical to the running one declares the same variables, so
        // none of them is new and the report is empty without being asked.
        let Some(diff) = difference(ctx, &previous.program.source, code, phase)? else {
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
            unreadable: ctx.unreadable_inputs(
                &self.branches[pred].record,
                &previous.program.ast,
                &planned,
            ),
        })
    }

    /// Replace `production` with the version `code` describes.
    ///
    /// Rejected when the new version cannot **take over the state**: every
    /// mutable variable the running program holds a value for must be one the
    /// new version still declares, at the same type, so that its value is seeded
    /// rather than discarded. Those are the refusals [`StateConflict`] names.
    /// Everything else is allowed: logic freely, sources and sinks by addition,
    /// and a variable moving to another loop, which seeds with the value it held
    /// and counts positions in whatever it now iterates.
    ///
    /// That is the whole guard, and it is narrower than it first looks. A
    /// version that adds an `http_serve` route serves it as soon as the swap
    /// completes, and one that stops serving a route retires it, so that address
    /// answers 404 rather than hanging. What is refused is a value that cannot
    /// be seeded, or cannot be seeded into a decided place, because that is the
    /// one outcome an author cannot see having happened: the program carries on
    /// answering and only the accumulated history is wrong. A version that
    /// retires a variable says where its value goes by reading it with
    /// `@LoadFrom`, and the other direction is refused too: a `@LoadFrom` naming
    /// a variable no running program holds.
    ///
    /// On `Err` the running program is untouched and still serving: both the
    /// compile to [`Phase::Planning`] and this check run before anything is torn
    /// down. That compile binds the ports the new version adds, so an address
    /// it cannot bind is one of the errors raised here rather than a failure of
    /// the compile that installs the version — which runs after the teardown and
    /// has nothing to reject to. A refusal hands those ports back.
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
    /// disagreement is a compiler bug — and one that has already taken the
    /// program down, which is not a state to hand back to a caller as a
    /// rejection.
    pub fn reload(
        &mut self,
        ctx: &mut GlobalContext,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, Vec<CompileError>> {
        self.reload_branch(ctx, ROOT, code, main_consumer)
            .map_err(|e| match e {
                BranchError::Compile(errs) => errs,
                other => {
                    unreachable!("the root is always in the table and never orphaned: {other}")
                }
            })
    }

    /// Replace branch `name`'s version with the one `code` describes.
    ///
    /// For `production` this is [`reload`](Self::reload). For any other branch
    /// the new version is diffed against its origin's running version, the state
    /// guard runs against the origin's variables, and the compile is offered the
    /// origin's entry: every operator it keeps is the origin's, subscribed through
    /// one more fan-out slot, and every store it rebuilds is seeded from the value
    /// the origin's variable holds now. The origin's entry is read and left as it
    /// was (`src/ccl/design/program-evolution.md`, "Reloading a branch forks it
    /// from its origin").
    ///
    /// The branch's previous operators are not offered, so a reload discards the
    /// branch's own history and re-forks it from the origin. They are released
    /// before the offer is made, where no other entry holds them: a source hands
    /// a new producer what every registered producer has left unreleased, and a
    /// branch's own previous producers left behind would have the rebuilt store,
    /// seeded from the origin's value, fold again what that value already
    /// summarizes.
    ///
    /// Refused for a branch the table does not hold and for an orphan, as well as
    /// for everything [`reload`](Self::reload) refuses; a refusal leaves every
    /// branch serving.
    ///
    /// # Panics
    ///
    /// As [`reload`](Self::reload).
    pub fn reload_branch(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
        code: &str,
        main_consumer: MainConsumerFactory<'_>,
    ) -> Result<ReloadReport, BranchError> {
        let at = self.index_of(name)?;
        let pred = self.predecessor_of(at)?;
        let is_root = pred == at;
        debug_assert_eq!(
            is_root,
            self.branches[at].origin == Origin::Root,
            "only the root is its own predecessor"
        );

        let diff = difference(
            ctx,
            &self.version_of(pred).program.source,
            code,
            Phase::AsOfRead,
        )?
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
        let conflicts = ctx.state_conflicts(&self.branches[pred].record, &planned);
        if !conflicts.is_empty() {
            ctx.sources_and_sinks_mut().release_unrouted_ports();
            return Err(BranchError::Compile(vec![state_refusal(&conflicts)]));
        }

        // Read before teardown, off the same planned tree the guard used, so this
        // and `/diff` answer alike and neither has to walk a graph that is gone.
        let unreadable = ctx.unreadable_inputs(
            &self.branches[pred].record,
            &self.version_of(pred).program.ast,
            &planned,
        );

        // Tear down this branch's graph, where no other entry runs it.
        let retiring = self.branches[at].version;
        self.release_version(retiring, at);
        let previous_record = std::mem::take(&mut self.branches[at].record);
        if is_root {
            // The root's predecessor is its own entry. The offer holds those
            // operators until conversion is over, as a single program's reload
            // always has.
            ctx.offer_predecessor(&previous_record);
            drop(previous_record);
        } else {
            drop(previous_record);
            ctx.offer_predecessor(&self.branches[pred].record);
        }

        let bound_elsewhere = self.routes_bound_except(at);
        // The tree the offered graph was built from is still here — a teardown
        // drops the producers, not the program — so the compile below can be
        // told which of its nodes the offer already has an operator for.
        let program = compile_replacement(
            ctx,
            code,
            main_consumer(),
            &self.version_of(pred).program.ast,
            &bound_elsewhere,
        )
        .expect("a version that compiled to Planning must compile to operators");
        let version = self.insert_version(Version::driving(program));
        let branch = &mut self.branches[at];
        branch.version = version;
        branch.record = ctx.take_record();
        branch.stale = false;
        let reloaded = Origin::Running(name.to_string());
        for child in &mut self.branches {
            if child.origin == reloaded {
                child.stale = true;
            }
        }
        self.collect_versions();
        Ok(ReloadReport {
            diff,
            reuse: ctx.reuse(),
            unreadable,
        })
    }

    /// Create branch `name` as a copy of branch `origin`'s entry: the same
    /// version, the same tree, the same operators and sink consumers.
    ///
    /// Nothing is compiled, built or subscribed, so the new branch runs from
    /// creation and every operator it holds is one its origin already runs.
    /// Refused when `name` is already in the table or is not a branch name; an
    /// orphan may be an origin.
    pub fn create_branch(&mut self, name: &str, origin: &str) -> Result<(), BranchError> {
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
        let from = self.index_of(origin)?;
        let copy = Branch {
            name: name.to_string(),
            origin: Origin::Running(origin.to_string()),
            stale: false,
            version: self.branches[from].version,
            record: self.branches[from].record.clone(),
        };
        self.branches.push(copy);
        Ok(())
    }

    /// Delete branch `name`'s entry.
    ///
    /// Its sink consumers are detached and its outputs dropped where no other
    /// entry runs its version, and its operators are freed where no other entry
    /// holds them; a freed producer's `Drop` returns its release record to the
    /// source it read. Every route no remaining branch binds is retired. Each
    /// branch whose origin was `name` becomes an orphan.
    ///
    /// Refused for `production` and for a name the table does not hold. Returns
    /// the names of the branches it orphaned.
    pub fn delete_branch(
        &mut self,
        ctx: &mut GlobalContext,
        name: &str,
    ) -> Result<Vec<String>, BranchError> {
        if name == ROOT {
            return Err(BranchError::Refused(format!(
                "`{ROOT}` is the root branch and cannot be deleted\n"
            )));
        }
        let at = self.index_of(name)?;
        self.release_version(self.branches[at].version, at);
        let removed = self.branches.remove(at);
        drop(removed.record);
        let deleted = Origin::Running(name.to_string());
        let mut orphaned = Vec::new();
        for child in &mut self.branches {
            if child.origin == deleted {
                child.origin = Origin::Deleted(name.to_string());
                orphaned.push(child.name.clone());
            }
        }
        self.collect_versions();
        let still_bound = self.routes_bound_except(usize::MAX);
        ctx.retire_routes_absent_from(&still_bound);
        Ok(orphaned)
    }

    /// Make `origin` the origin of branch `name`, and mark `name` stale.
    ///
    /// Nothing running changes: the next reload of `name` diffs against and
    /// forks from `origin`. Clears orphan status. Refused for `production`,
    /// which has no origin; for a name or an origin the table does not hold; and
    /// for an `origin` that is `name` or descends from it, which would make the
    /// chain of origins a cycle with no root.
    pub fn retarget_branch(&mut self, name: &str, origin: &str) -> Result<(), BranchError> {
        if name == ROOT {
            return Err(BranchError::Refused(format!(
                "`{ROOT}` is the root branch and has no origin to retarget\n"
            )));
        }
        let at = self.index_of(name)?;
        let mut cursor = self.index_of(origin)?;
        // Walk the new origin's chain towards the root. It ends at the root or at
        // an orphan, because every retarget runs this check and a branch is only
        // ever created onto a branch that already exists.
        let mut walked = 0;
        loop {
            if cursor == at {
                return Err(BranchError::Refused(format!(
                    "`{origin}` is `{name}` or descends from it, so retargeting `{name}` onto it \
                     would make the chain of origins a cycle with no root\n"
                )));
            }
            match &self.branches[cursor].origin {
                Origin::Running(next) => cursor = self.index_of(next)?,
                Origin::Root | Origin::Deleted(_) => break,
            }
            walked += 1;
            debug_assert!(
                walked <= self.branches.len(),
                "the chain of origins is acyclic, so a walk visits each branch at most once"
            );
        }
        let branch = &mut self.branches[at];
        branch.origin = Origin::Running(origin.to_string());
        branch.stale = true;
        Ok(())
    }

    /// End the subscriptions of `version`, the one the entry at `at` runs, where
    /// no other entry runs it too.
    ///
    /// The one place the ownership check on sink consumers is written out. A
    /// sink consumer needs an explicit [`SinkConsumer::detach`] to stop
    /// dispatch, and a version's sink consumers are shared exactly with the
    /// version, so a branch detaches only the ones no other entry holds.
    ///
    /// [`SinkConsumer::detach`]: crate::interpreter::SinkConsumer::detach
    fn release_version(&mut self, version: VersionId, at: usize) {
        let held_elsewhere = self
            .branches
            .iter()
            .enumerate()
            .any(|(other, b)| other != at && b.version == version);
        if !held_elsewhere {
            self.versions
                .get_mut(&version)
                .expect("an entry names a version the table holds")
                .tear_down();
        }
    }

    /// Drop every version no entry names.
    fn collect_versions(&mut self) {
        let named: HashSet<VersionId> = self.branches.iter().map(|b| b.version).collect();
        self.versions.retain(|id, version| {
            let keep = named.contains(id);
            debug_assert!(
                keep || version.program.outputs.is_empty(),
                "a version is torn down before the last entry naming it lets go of it"
            );
            keep
        });
    }

    /// The union of the routes every branch but the one at `at` runs a version
    /// binding. `usize::MAX` excepts none.
    fn routes_bound_except(&self, at: usize) -> HashSet<String> {
        self.branches
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != at)
            .flat_map(|(_, b)| self.versions[&b.version].program.routes.iter().cloned())
            .collect()
    }
}
