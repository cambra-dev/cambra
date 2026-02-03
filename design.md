Pototo is a programming language that implements a new programming paradigm.
It abstracts over low level concepts like memory, threads, and connections, enabling programmers to focus on the logic of their program, non-functional requirements, and high-level architectural decisions.
The denotational semantics of the language is a pure, dependently-typed, functional language.
The operational semantics is very unlike the lambda calculus: rather than operating via term-wise beta reduction, function terms implement a producer/consumer interface which allows the runtime to implement streaming dataflow semantics, with pipelining, parallelization, and vectorization.
Progress is tracked by sending puntuations through this producer/consumer interface.


* Python syntax
    * Programs are written in a Pythonic syntax that uses for-comprehensions for the definition of collection-level logic. This Python syntax is lowered to the Pototo Core Language (PCL), where it is typechecked and interpreted.
    * Supported: functions, type annotations, assignment, augmented assignment, operators, assignment expressions, attributes, kwargs, ...
    * Likely need some customizations (defer for now):
        * Multi-line generator expressions, so generators don't always have to be wrapped in a def
        * A way to define records. Could reuse Python classes, but they're really imperative and full of boilerplate.
    * Need to lower to PCL. Will defer until after hashing out the fundamental pieces of PCL and the interpreter.
        * Retain location info through lowering
        * Big challenge is converting imperative loops into functional expressions. In particular, defining the indexing for these definitions is a big unknown.
        * Converting comprehensions & generators should be easier: just make them lambdas, with some additional indexing for each `yield`

* Pototo Core Language (PCL)
    * Should be really simple: literals, variables, records, unions, lambdas, let-binding, application, pattern matching, type annotations.
    * Will want a type checker, but can defer implementing it until later, and just make sure terms typecheck when experimenting.
    * To execute PCL, we convert each term in the AST into a dataflow operator and wire them up to execute.
        * The interpreter walks the AST, converting AST nodes into dataflow operators, and kicking off computation by subscribing to a dataflow operator when forced.
        * Each operator has an **extent**, the set of values the term can take on, and corresponding exactly to the term's type.
        * Execution proceeds by working in terms of **regions**, which are subsets of the extent: operators can ask for regions, inform about the availability of a region, and revoke their interest in a region.
        * A region is represented by a **guard** which is a data structure respresenting a set of predicates, such as equalities, set memberships, and inequalities.

    * Dataflow operators implement a producer/consumer protocol:
        * Subscribe(Guard, Consumer, VarScope): the consumer registers interest with the producer in a region of the producer's extent using an **intent guard**. The `VarScope` parameter provides variable context for operators that reference variables.
        * Notify(Guard): the producer notifies the consumer that data is ready for it to retrieve, along with a **yield guard** specifying a region that will not see any further data.
        * Get: the consumer requests the data that is ready from the producer and gets it synchronously. The data structure that represents data is determined by the operator's type: records have multiple fields, unions have multiple cases, and lambdas are collections. These types can be nested, and the data structure explicitly tracks that nesting. 
        * Release(Guard): the consumer retracts interest in a sub-region of its subscription with the producer in the form of an **obsolete guard**.

    * **Operator vs Runtime State**: There is an important distinction between operators and runtime state:
        * **Operators** are stateless and correspond to program syntax. They implement the `Operator` trait and include: `Literal`, `Var`, `VarRef`, `Lambda`, `Application`, etc. Each operator has an extent (its type) but no runtime state.
        * **Producers and Consumers** are runtime stateful objects created when `subscribe()` is called on an operator. They implement the `Producer` and `Consumer` traits respectively, and maintain all the runtime state needed for dataflow execution (yield guards, consumers lists, etc.).
        * When `Operator::subscribe()` is called, it creates the appropriate producer/consumer objects and wires them up according to the operator's semantics.

    * **Guard Monotonicity Contract**: The contract of `Consumer::notify()` guarantees that yield guards are **monotonically growing**. That is, each call to `notify()` must provide a yield guard that is a superset (or equal to) all previous yield guards for that consumer. This contract allows implementations to store a single yield guard rather than tracking all historical guards, and enables efficient guard management throughout the dataflow graph. 

# PCL operators:
## Literals
Subscribe calls Notify on the consumer immediately. Notify calls Get. Get returns a constant. Release is a no-op.

## Variables

Variables are split into operators and runtime state:

### Var Operator
A `Var` operator represents a variable definition. It holds:
    * The variable's name
    * The extent of this variable
    * A predicate guard that restricts the variable's extent (may reference outer variables for correlated scans)

Note: `Var` does **not** hold a static definition. Binding happens dynamically:
- When the lambda is **applied**, the `Application` operator binds the argument to the variable
- When the lambda is **aggregated** (e.g., by `sum`), the variable remains unbound and scans its extent

The variable is owned and managed by the operator that defines it (record, lambda, let-binding, pattern match).

### VarSub (Runtime State)
A `VarSub` is created when `Var::subscribe()` is called. It can operate in two modes:

**Bound Mode** (lambda applied to argument):
    * Wraps a producer from the binding expression
    * Forwards values from that producer

**Scanning Mode** (lambda aggregated):
    * Iterates over the variable's extent
    * Applies predicate to filter values
    * For correlated predicates (referencing outer variables): executes as a join
    * Produces `parent_indices` relating scan results to outer scans

Common to both modes:
    * Maintains a list of all consumers that have subscribed to this variable
    * Stores a release guard for use by variable references
    * Stores `parent_indices` for alignment (scanning mode only)

```rust
enum VarSource {
    Bound(Box<dyn Producer>),
    Scanning {
        extent: Extent,
        predicate: Guard,
        correlations: Vec<Correlation>,  // outer variables in predicate
    },
}

struct Correlation {
    outer_variable: String,
    join_strategy: JoinStrategy,
}

enum JoinStrategy {
    CartesianProduct,
    HashJoin { key_expr: Expr },
    // Future: IndexLookup, MergeJoin, etc.
}
```

When release is called on a function, its domain release guard is stored in the `VarSub` for use within the function body.

### VarRef Operator
A `VarRef` operator represents a reference to a variable. It holds:
    * The name of the variable being referenced
    * The extent (cached from the variable when found)

### VarRefSub (Runtime State)
A `VarRefSub` is created when `VarRef::subscribe()` is called. It implements `Producer`:
    * Filters data from the `VarSub` based on its intent guard
    * **Handles alignment**: If referencing an outer variable from within an inner scan, expands values using the inner scan's `parent_indices`
    * When `release()` is called, returns the stored release guard from the `VarSub` rather than invoking release on the subscription itself (since the lambda would have already invoked it)

```rust
struct VarRefSub {
    var_sub: Rc<RefCell<VarSub>>,
    intent_guard: Guard,
    consumer: Box<dyn Consumer>,
    // The innermost scan in scope (for alignment)
    innermost_scan: Option<Rc<RefCell<VarSub>>>,
}
```

The `innermost_scan` is set by `VarScope` when the variable is looked up. If the referenced variable is from an outer scope and there's a scanning variable at an inner level, alignment is needed.

### Variable Lookup: VarScope
Variables are looked up by name using a `VarScope` structure:
    * `VarScope` is a linked list structure that maps variable names to their `VarSub` objects
    * Supports parent chaining for nested scopes (e.g., lambdas within lambdas)
    * When looking up a variable, the scope searches up the parent chain if not found in the current scope
    * `VarScope` is passed through `subscribe()` calls to enable variable lookup

### Variable System Flow

The variable system works as follows:

1. **Variable Definition**: When `Var::subscribe()` is called:
    * Creates a `VarSub` 
    * Adds the original consumer (from the subscribe call) to the subscription's consumers list
    * Uses the subscription itself (wrapped in `Rc<RefCell<>>`) as the consumer for the definition operator
    * Subscribes to the definition operator
    * Returns the subscription as a producer

2. **Variable Reference**: When `VarRef::subscribe()` is called:
    * Looks up the variable name in the provided `VarScope` (searching up the parent chain if needed)
    * Adds itself as a consumer to the found `VarSub`'s consumers list
    * Creates and returns a `VarRefSub` that filters data based on the intent guard

3. **Notification Flow**: When the definition operator notifies:
    * Notification goes to `VarSub::notify()`
    * The yield guard is updated 
    * All registered consumers (including all `VarRefSub`s) are notified with the updated yield guard

4. **Data Access**: When a `VarRefSub` calls `get()`:
    * It retrieves data from the `VarSub`
    * Filters the data based on its intent guard 
    * Returns the filtered data

5. **Release Flow**: When a `VarRefSub` calls `release()`:
    * Returns the stored release guard from the `VarSub`
    * Does not propagate release to the definition (the lambda handles that)

### Quantification and Variable Binding Modes

Variables are quantified as either existential or universal:
- **Existential** (let-bindings, records, patterns): Single definition, variable is always **bound**
- **Universal** (lambda variables): Can be bound or scanned depending on context

Lambda variables have two modes:

| Mode | When | Behavior |
|------|------|----------|
| **Bound** | Lambda is applied (`(\x. body) arg`) | Variable forwards values from argument expression |
| **Scanning** | Lambda is aggregated (`sum(\x. body)`) | Variable scans over its extent (like a table scan) |

A problem arises when there are multiple variables in **scanning mode** in the same scope (i.e. nested lambdas being aggregated): the different variables need to be aligned with respect to each other so that expressions over both of them evaluate over corresponding values.

### Columnar Values and Alignment

To support vectorized execution, `Value` is extended to a columnar representation:

```rust
struct ColumnValue {
    values: Vec<ScalarValue>,
    // Indices into parent level's batch (for alignment with outer scans)
    // None if this is the outermost level or independent
    parent_indices: Option<Vec<usize>>,
}
```

When evaluating expressions with multiple universally-quantified variables in scope, `parent_indices` tracks which values correspond to which "rows" of the enclosing scan. This enables:
- Proper alignment of values from different nesting levels
- Efficient join execution between nested scans
- Vectorized operations on aligned batches

### Scans as Joins

When there are nested scanning lambdas, the execution is conceptually a join:

```
sum(\t1. sum(\t2. f(t1, t2)))
```

This is equivalent to:
```sql
SELECT sum(f(t1, t2)) FROM t1, t2 [WHERE predicate]
```

Join behavior depends on predicates:
- **No predicate**: Cartesian product (cross join)
- **Equality predicate** (`t2.fk = t1.pk`): Hash join or index lookup
- **Other predicates**: Filter after join, or specialized index structures

The `parent_indices` in a `ColumnValue` are the output of the join algorithm—they indicate which outer row each inner row is paired with.

### Alignment via VarRefSub

When a `VarRef` references an outer variable from within an inner scan, the `VarRefSub` handles alignment:

1. `VarScope` tracks the **innermost scan** in scope
2. When `VarRefSub::get()` is called for an outer variable:
   - Get the outer variable's values
   - Get `parent_indices` from the innermost scan
   - Expand outer values: `outer_values[parent_indices[i]]` for each `i`
3. All values at the innermost level are now aligned and can be zipped by operators


### Example: Nested Scans

For `sum(\t1. sum(\t2 where t2.fk = t1.pk. v(t1) + v(t2)))`:

1. **Outer scan (t1)** yields batch: `[A, B, C]`

2. **Inner scan (t2)** sees predicate `t2.fk = t1.pk`:
   - Recognizes correlation with `t1`
   - Uses hash join: builds hash table on `t1.pk`, probes with `t2.fk`
   - Yields matching rows with `parent_indices`

3. **t2 batch**:
   ```
   values: [t2_row1, t2_row2, t2_row3, t2_row4]
   parent_indices: [0, 0, 1, 2]  // rows 1,2 match A; row 3 matches B; row 4 matches C
   ```

4. **VarRef for t1** (inside inner body):
   - Gets t1 values: `[A, B, C]`
   - Expands using t2's parent_indices: `[A, A, B, C]`
   - Now aligned with t2 values

5. **v(t1) + v(t2)** operates on aligned batches of length 4

### VarScope: Using Parent Chain for Multi-Level Alignment

Each `VarScope` contains exactly one variable (the lambda's bound variable). The parent scope
chain serves as the natural scan chain - no separate tracking needed.

**Problem:**
```
sum(\t1. sum(\t2. sum(\t3. v(t1) + v(t2) + v(t3))))
```
When referencing `v(t1)` from t3's context:
- t3's parent_indices = [0,0,1,1,2,2] (maps to t2)
- t2's parent_indices = [0,0,1] (maps to t1)
- Must compose: `[0,0,0,0,1,1]` by chaining through t2.

**Simplified VarScope:**
```rust
pub struct VarScope {
    parent: Option<Box<VarScope>>,
    name: String,                        // Single variable name
    subscription: Rc<RefCell<VarSub>>,   // Single variable subscription
}
```

**lookup_variable() walks parent chain:**
```rust
/// Returns (found_subscription, inner_scans) where inner_scans is the chain
/// of scanning variables between current scope and the found variable.
pub fn lookup_variable(&self, name: &str) -> Option<(Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>)> {
    self.lookup_with_chain(name, Vec::new())
}

fn lookup_with_chain(&self, name: &str, mut chain: Vec<Rc<RefCell<VarSub>>>) 
    -> Option<(Rc<RefCell<VarSub>>, Vec<Rc<RefCell<VarSub>>>)> {
    if self.name == name {
        Some((self.subscription.clone(), chain))
    } else {
        // If this scope's variable is scanning, add it to the chain
        if self.subscription.borrow().is_scanning() {
            chain.push(self.subscription.clone());
        }
        self.parent.as_ref()?.lookup_with_chain(name, chain)
    }
}
```

**VarRefSub::get() composes parent_indices:**
```rust
fn compose_indices(outer: &[usize], inner: &[usize]) -> Vec<usize> {
    inner.iter().map(|&i| outer[i]).collect()
}

fn get(&mut self) -> ColumnValue {
    let column = self.variable_subscription.borrow_mut().get();
    
    if self.scan_chain.is_empty() {
        return column;
    }
    
    // Compose parent_indices from innermost to outermost
    let mut indices: Option<Vec<usize>> = None;
    for scan in self.scan_chain.iter().rev() {  // innermost first
        if let Some(parent_indices) = scan.borrow_mut().get().parent_indices {
            indices = Some(match indices {
                None => parent_indices,
                Some(inner) => compose_indices(&parent_indices, &inner),
            });
        }
    }
    
    match indices {
        Some(idx) => column.expand(&idx),
        None => column,
    }
}
```

## Records
A record is a map of field names to field definitions. Each field's definition is a dataflow operator. Subscribe splits the provided guard into a guard for each field, and calls subscribe on each corresponding field's operator. Notify is called by each field's operator when ready. Get zips together the data for the record's fields (TODO: how do we handle alignment when some fields of a record are ready, but others aren't? Maybe we only return when all subscribed fields are available). Release splits the obsolete guard and propagates the subguards to each field (TODO: how to handle correlated guards?).

## Application
Applies a function to an argument by resolving the argument and propagating it to the function. 

Subscribe receives an intent guard for the function's codomain. It uses the function's dep-rel to generate the depends-image of the codomain intent guard, and subscribes to the argument with the resulting domain intent guard. It then subscribes to the function with the combined domain/codomain intent guards (NOTE: the choice of eager/lazy evaluation is decided here by whether subscribe is invoked on the function before or after the argument notifies). 

Notify is forwarded from the argument to the function. Get gets from the argument and function, and returns the corresponding elements of the codomain. 

Release is implemented as the following pseudocode:
```
def release(g_c):
    g_d1 = f.pre(g_c) # generate an initial obsolete guard for the domain
    g_d2 = arg.release(g_d1) # release the argument, and get back an expanded obsolete guard for the domain.
    # g_d1 ⊂ g_d2 , but g_d2 can be larger if `arg` has a variable with its own obsolete guard
    g_fn = fn.release(fn.extent().create_from_parts(g_d2, g_c)) # release the function by combining the domain and codomain guards into a single unified guard
    # TODO: what if g_fn.split_domain() is a strict superset of g_d2? Would this process ever need to be iterated to guarantee release of all resources?
    return g_fn.split_codomain()
```
This approach allows obsolescence to flow bidirectionally within the lambda's body. 
It flows upstream from the top node of the body starting with the lambda's codomain obsolete guard. 
It flows downstream from the variables with the lambda's domain obsolete guard. 
These flows meet at application nodes, where obsolescence information comes from the function's codomain _and_ its domain (if the function argument uses a variable from an enclosing lambda).
To handle this, we first flow obsolescence upstream to the argument by generating an obsolence guard as the preimage of the codomain guard, which returns an updated domain obsolescence guard.
Then, we use that updated domain guard together with the original codomain guard to release the function.
Most of the time, this complex flow boils down to "get a domain guard from the argument and use it on the function" (i.e. unidirectional flow), but supporting this bidirectional flow is critical to ensure garbage collection doesn't leak resources as complex programs are composed together.


## Lambdas
A lambda is a (universally quantified) variable and a body, which can be applied to another term to replace the variable with that term. To accomplish this, the lambda operator manages a Var. 

Subscribe splits its intent guard into domain and codomain intent guards, then calls subscribe on its variable and body with these guards. 

Notify comes from the variable, and is handled by the Var. Get returns a collection of function bindings. 

Release splits the obsolete guard on domain and codomain, and calls release on the Var and the body with the corresponding guard. The Var stores its obsolete guard until the release call on the body returns so that variable references in the body can return expanded obsolete guards as needed.


## Memos
A memo is a function that stores its bindings so they don't have to be recomputed in the future. 
It takes a function as an argument and proxies all requests to/from it, but with additional logic to store, get, and release bindings.
The memo manages subscriptions to its argument in a way that guarantees that the same bindings are never computed twice. (TODO: would we want different kinds of memos, e.g. LRU memo with fixed size?)
Subscriptions to the memo keep track of which bindings are already stored in the memo (and can therefore notify), and which are still outstanding.
To implement this, the memo keeps a yield guard to track how much of extent is ready, as well as an obsolete guard to track which parts have expired. 

Subscribe first checks whether the current yield guard covers the intent guard. If it does not, it looks at the memo's subscription's intent guard to see if it can be reused. If not, it cancels that subscription and creates a new memo subscription for the union of the previous and new intent guards. It the creates and returns a new subscription for the given intent guard.

Notify:
* Calls Get immediately and stores all the returned bindings
* Calls Release with the yield guard to release its interest in that region of the extent
* Issues notify calls for all downstream subscriptions with overlapping intent guards

Get returns a handle to the data structure currently held in the memo, filtered to the subscription's intent guard. This data structure is indexed by the memo's domain, and can be filtered efficiently along that axis, or scanned fully.
No data is returned for regions that have been released by all subscriptions.

Release drops bindings for the given obsolete guard. It does not propagate upstream because memo releases data as soon as it is Notified.


## Let-bindings: 

## Unions, dependent records: TODO

## Pattern matching: 


# How to handle Cycles
Many of the above algorithms will not terminate if there's a cycle in the dataflow graph. How do we need to modify them to ensure termination? In which cases can we ensure convergence rather than simply truncating the iteration?


# Open Challenges / Deferred Work

## Streaming Joins
The current join design assumes nothing happens until all data has been scanned. For true streaming joins, where yield guards advance gradually:
- How do we execute joins incrementally as new batches arrive?
- When can we emit partial results vs. waiting for a universal yield guard?

Potential approaches:
- Symmetric hash join: build hash tables on both sides, emit matches as data arrives
- Windowed joins: partition by time/sequence and join within windows

## Guard Expression Evaluation
The current design assumes guards can be evaluated, but complex guard expressions present challenges:
- Guards may contain arbitrary expressions (e.g., `t2.fk = t1.pk + 1`)
- These expressions need access to variable values, which requires the dataflow machinery
- Circular dependency: need to evaluate guard to set up dataflow, but need dataflow to evaluate guard. 

Potential approaches:
- Restrict guards to simple predicates (equality on columns)
- Set up dataflow operators to compute these guards and feed them into the operators that need them
- Two-phase evaluation: first pass extracts guard structure, second pass evaluates

## Multi-Level Nesting Optimization
For deeply nested scans (`\t1. \t2. \t3. ...`):
- Composing parent_indices through multiple levels may be inefficient
- May want to precompute transitive indices (t1→t3 directly)
- Trade-off between space (storing more indices) and time (recomputing)


# PCL Proof of Concept
    

* PCL interpreter
    * Convert to dataflow operators and schedule.
    * Follow pull/push/progress protocol.
    * TODO: which cases can't be converted into dataflow?