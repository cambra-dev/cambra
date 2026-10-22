# CHL changes: modules, traits, collections and feeds

A summary of the language changes in two PR stacks, for discussion. Each item is marked
**merged**, **open** (a draft or review PR), or **planned**. The rules themselves are in
`docs/chl-spec.md`; section names are given where a change has one.

The two stacks:

- **Modules** (section 9 of the spec): a program spans several files.
- **Nominal types, traits and collections** (GitHub stack #445): user traits, then a series of
  changes to feeds, loops and collection types.

---

## Modules

### Importing (merged)

- **A program loads every module it reaches** through `import` and `run`, and refuses a missing
  module or a cycle (#353).
- **`import m` and `import a::b as c`** reach a module's `pub` members as `m::f`, as values,
  callees, and label or tag qualifiers (#360). `import m use f, T as U` brings members into scope
  by name; a local shadows a `use` name (#361).
- **Record labels and variant tags belong to a module** (spec 9.12, #359): `f1` in two modules is
  two labels, and an imported member prints qualified, `catalog::limit` (#363).
- **Type aliases export** as `m::T` and through `use` (#364). An alias's refinement reads names
  where the alias is declared, not where it is used (#362).
- **Importing asserts no IO and no state** (spec 9.7, #365). A module that declares mutable state
  cannot be imported; a shared function over state takes the caller's variables as `Mut`
  parameters, and those calls now compile.
- **An import may pass arguments**, `import m(x=1)`, with one shared run per module and set of
  arguments (#375). Arguments are literals for now.

### Runs and parameters (merged)

- **`run m as n`** performs a module's whole top level at its statement, with its own state,
  sinks and routes; its members are `n::f`, `n::T`, or reached through `use` (#369).
- **Value parameters**: `param step: Int = 1` in a module, passed as
  `run stepper(base=10, step=5) as a`, any expression above the statement (#370).

### Module types and type parameters (open)

- **Module types** (spec 9.8, #376): a parameter can take a module,
  `param pricing: Module{price: Int => Int}`; a `run` or `import` passes one; a module can
  hand back a run as a public member (`pub k = c`).
- **Type parameters**: `param T <: B = D`, passed as `run box(T=Int, x=3) as b` or
  `import holder(T=Int)`. Each run is checked at its arguments (#378).
- **Type members** in Module types, in three forms: `Name = T`, `Name <: T`, `Name: K`. An
  abstract member is filled by the argument module's own type, so a module can write
  `keep: Count => Count` against its parameter and receive the argument's `Count` (#383).

### Checking modules (open)

- **Each module is checked on its own** before the linked program is inferred, with its
  parameters abstract. Each `run` and `import` argument is checked against what its parameter
  states, and an error in a module is reported once, not once per run (#387).
- **`cambra check lib.cambra`** checks a file alone and prints its interface: its parameters and
  public members with their types (spec 9.14, #389).
- **A link-time error names the run** whose copy raised it; copies that fail alike merge into one
  error labelled at every run (#395).

### Nominal types across modules, and `const` (open)

- **Any module can declare and export a `type`**, its associated functions and `impl` blocks. A
  type's identity includes the module type arguments it reaches, so two runs with different
  arguments hold two types (#481).
- **Calls take `name=value` arguments**, so another module can build a record payload with the
  declaring module's labels: `shop::Amount::new(shop::amount=3)` (#481).
- **A method resolves on a type the calling module neither imports nor runs**, as when a run
  returns another module's type (#482).
- **`const`** marks a binding or a value parameter fixed once the program links:
  `const limit = max_rate * 2`, `const param max_rate: Int` (#485). A `type` declaration's
  refinement may name constants, and a type reaching a `const` parameter is one type per value
  its runs give it.

---

## Nominal types and traits

### Nominal type basics (merged)

Spec 6.8, "Nominal types and methods" (#377, #379, #380, #390).

- **A `type` declaration lists constructors**, each a function building the type's values, or a
  value when it takes no parameters. The single-constructor form `type N = R` declares one
  constructor, `N::new`, and the method `extract` that returns its argument:

  ```python
  type Shape:
      circle(radius: Int)
      rect(w: Int, h: Int)
      empty

  type Price = {Int where _ >= 0}      # Price::new(5), p.extract()
  type Box(T) = T                      # parameterized: Box::new("hi") is a Box(String)
  ```

- **A refinement in a declaration is checked at every construction.** `Price::new(-1)` is an error,
  so every `Price` holds a non-negative value.
- **A nominal type is opaque.** It relates only to itself and its refinements: a `Price` is not an
  `Int`, and two declarations of one shape are two types. A parameter's variance comes from the
  constructors' parameter types, so `Option` is covariant in `T`.
- **`match` takes a value apart by constructor**, and must cover every constructor:

  ```python
  def Shape::area(self) => Int:          # a method: an associated function taking `self`
      match self:
          case Shape::circle(r):
              3 * r * r
          case Shape::rect(w, h):
              w * h
          case Shape::empty:
              0
  ```

- **Associated functions and methods** are declared as `def T::f(…)` or together in an `impl`
  block. A method is called `s.area()` or `Shape::area(s)`, and `Shape::area` alone is the
  function value:

  ```python
  impl Price:
      def larger(self, other: Price) => Price:
          self if self.extract() >= other.extract() else other

  impl Box(T):                           # binds T once for every def in the block
      def get(self) => T:
          self.extract()

  sum([s.area() for s in [Shape::circle(2), Shape::rect(3, 4), Shape::empty]])    # 24
  Price::new(5).larger(Price::new(7)).extract()                                   # 7
  ```

- **`Option(T)` is a compiler-provided nominal type** with constructors `some(T)` and `none`.
  The checked lookup `m[k]?` answers one:

  ```python
  def or_zero(o: Option(Int)) => Int:
      match o:
          case Option::some(v):
              v
          case Option::none:
              0

  m = map(["a" -> 1, "b" -> 2])
  or_zero(m["b"]?) + or_zero(m["z"]?)    # 2
  ```

The rest of this section is **open**, in stack #445.

### User traits

- **A module declares a trait** with operands, associated types, function signatures and a
  `requires` clause, and **instances** with `impl Trait(…)` over its nominal types (#421):

  ```python
  trait Area(S):
      def area(s: S) => Int

  impl Area(Square):
      def area(s):
          s.extract() * s.extract()

  Area::area(sq)
  ```

  A trait's functions are called through the trait's name, never as methods: no parameter of one
  is named `self`, and `sq.area()` calls only a method `Square` itself declares. A generic `def`
  calls a trait function on a type parameter through `requires Area(S)`. Dispatch is static: each
  call resolves to the one instance its types match.

- **Comparison is opt-in and by value** (spec "Equality and order", #434). A bodiless
  `impl Equatable(Money, Money)` gives `==`, and `impl Orderable(Money, Money)`, which requires
  the first, gives ordering, `max`/`min`, and use as a `groupby`, `map` or join key. Order is the
  declaration's: parameters in order, a written record by its fields. No instance defines its own
  `==`.
- **Tuples order lexicographically** under `Orderable`, `max` and `min`; records still do not
  (#438).
- **Arithmetic operators are definable**: `impl Addable(Money, Money, Output=Money)` with an
  `add` function defines `+` on `Money`. The same goes for `-`, `*`, `//`, `**` and unary `-`,
  and each function is callable by name: `Addable::add(a, b)` (#439).

---

## Feeds, patterns and loops (open, stack #445)

- **Tuple patterns in `=`**: `(a, b) = f()`, with or without parentheses (#476). `http_serve`
  becomes an ordinary call returning a tuple.
- **Feeds are declared**, and `defer()` is gone (#477):

  ```python
  out: Feed(Int)
  for x in xs:
      out << x * 2
  ```

  A `def` parameter may also be a `Feed(…)`.
- **Loop and comprehension binders take patterns**: `for (k, v) in pairs`,
  `[a + b for (a, b) in ps]`. `_` binds nothing (#478).
- **Every loop iterates through the `Iterable` trait** (#480): `for x in c` reads
  `Iterable::elements(c)`. A structural collection is its own elements, and a user type can
  provide an instance.

## Collection types (open, stack #445)

- **Data-function type `D |=> V`** (spec 6.3, #483): a collection over the domain `D` with
  values `V`, written wherever `T => U` is.
  - A domain written as `_` or a type parameter also admits a boxed collection (`List`, `Map`,
    `box(…)`): `_ |=> V` is an inferred annotation, looser than `Collection(V)`.
  - A written domain names a plain collection: `String |=> Int`.
  - Diagnostics print collections this way: `{String where _ in ["a", "b"]} |=> Int` rather than
    `FullMap(…)`.
- **Bounded associated types** (#484): `type Elements <: _ |=> _` in a trait. A requirement
  reads one by pattern, so a generic function can loop over any collection:

  ```python
  def largest(C, T, c: C) => T requires Iterable(C, Elements=_ |=> T), Orderable(T, T):
      max([x for x in c])
  ```

- **Dependent function types**: `(x: T) => U` and `(k: D) |=> V`, where the codomain reads the
  argument; `FullMap(k: K, V)` names its key the same way (#487). A `groupby`'s type is one:
  each group's domain reads its key.
- **Binding parameters on `type`** (spec "Binding parameters", #487): a parameter `k: K` binds
  `k` in the parameters after it, and the declaration's body reads it under a function binding
  `k`:

  ```python
  type Groups(k: K, V) = (k: K) |=> V
  g = Groups::new(groupby([1, 2, 3], \x -> x > 1))
  ```

  An application may name the binder: `Groups(k: SKU, {Int where _ > len(k)})`.
  - **Known gap:** a generic function returning a dependent collection cannot be iterated yet.
    It is fixed by work in another open stack, and closes once that merges.

### Planned

- **Nominal `Set`, `Map` and `FullMap`.**
  - `Map(K, V)` and `Set(K)` erase the key domain (they hold a boxed collection);
    `map([…])` and `set([…])` build them.
  - `FullMap(k: K, V)` keeps its domain, and `full_map(entries)` builds one where the keys
    provably equal `K`. `groupby` returns one.
  - Each iterates through an `Iterable` instance: a map's entries keyed by its own keys,
    `for k -> v in m`; a set's keys.
  - `keys()`, `values()`, `items()`; `sum(m)` over a map is refused.
- **Keyed feeds, `FeedMap(K, V)`.**
  - Written `out[k] = v`, with at most one value per key.
  - The key must be the position of the loops enclosing the write: their binders, or a tuple of
    them. Mutually exclusive `if` and `match` arms count as one write.
  - `http_serve` returns `(Map(RequestId, Body), FeedMap(RequestId, Response))`, so the
    request/response pairing is ordinary code.
- **A CHL prelude**, once modules land: `Iterable` and the collection types declared in source
  rather than by the compiler.

---

## Worked examples

The examples in the first two subsections run on the top of stack #445. Those in the third run on
the top of the modules stack. The last is specified but needs both stacks merged.

### Traits and parameterized types in one module

Operator and comparison instances, a parameterized type, a trait with an associated type, a
generic instance, a trait that requires another, and a generic function over any collection:

```python
type Money = Int

impl Equatable(Money, Money)
impl Orderable(Money, Money)           # requires the Equatable instance above

impl Addable(Money, Money, Output=Money):
    def add(x, other):
        Money::new(x.extract() + other.extract())

type Tagged(T):
    tagged(label: String, value: T)

trait Valued(T):
    type Value
    def value(t: T) => Value

trait Scored(T) requires Valued(T):    # every Scored instance needs a Valued one
    def score(t: T) => Int

impl forall (T) Valued(Tagged(T), Value=T):    # one instance for every Tagged(T)
    def value(t):
        match t:
            case Tagged::tagged(_, v):
                v

impl Scored(Tagged(Money)):
    def score(t):
        Valued::value(t).extract()

def best(C, T, items: C) => Int requires Iterable(C, Elements=_ |=> T), Scored(T):
    max([Scored::score(i) for i in items])

stock = [Tagged::tagged("pen", Money::new(2)), Tagged::tagged("lamp", Money::new(30))]
best(stock)                                # 30
(Money::new(3) + Money::new(4)).extract()  # 7
```

A trait over two types, and conditional instances whose `requires` recurse into a type's
argument. A requirement implies the requirements of its trait, so `closer` may call `same` though
it states only `Ranked`:

```python
type Meters = Int
type Pair(T) = {T, T}

trait Same(A, B):
    def same(a: A, b: B) => Bool

trait Ranked(A, B) requires Same(A, B):
    def rank(a: A, b: B) => Int

impl Same(Meters, Meters):
    def same(a, b):
        a.extract() == b.extract()

impl Ranked(Meters, Meters):
    def rank(a, b):
        a.extract() - b.extract()

impl forall (T) Same(Pair(T), Pair(T)) requires Same(T, T):
    def same(a, b):
        (a0, a1) = a.extract()
        (b0, b1) = b.extract()
        Same::same(a0, b0) and Same::same(a1, b1)

impl forall (T) Ranked(Pair(T), Pair(T)) requires Ranked(T, T):
    def rank(a, b):
        (a0, a1) = a.extract()
        (b0, b1) = b.extract()
        Ranked::rank(a0, b0) + Ranked::rank(a1, b1)

def closer(T, x: T, y: T) => Int requires Ranked(T, T):
    0 if Same::same(x, y) else Ranked::rank(x, y)

a = Pair::new((Meters::new(5), Meters::new(9)))
b = Pair::new((Meters::new(2), Meters::new(4)))
closer(a, b)                           # 8
```

### Dependent types through a nominal type

```python
type Groups(k: K, V) = (k: K) |=> V

gs = Groups::new(groupby([1, 2, 3], \x -> x > 1))
match gs:
    case Groups::new(g):
        sum([sum(grp) for grp in g])    # 6: each group's type reads its key
```

### Nominal types across modules

A module whose types depend on its parameters: a type parameter `Receipt` and a constant
`max_order`. Each run gets its own `Order`:

```python
# shop.cambra
param Receipt
const param max_order: Int

pub type Order:
    placed(receipt: Receipt, total: {Int where _ <= max_order})

pub def Order::total(self) => Int:
    match self:
        case Order::placed(_, t):
            t
```

```python
# deploy.cambra
run shop(Receipt=String, max_order=100) as eu
run shop(Receipt=Int, max_order=500) as us

a = eu::Order::placed("r-1", 80)
b = us::Order::placed(7, 450)
a.total() + b.total()                  # 530

eu::Order::placed("r-2", 450)          # error: expected {Int | __elem <= 100}

def total_eu(o: eu::Order) => Int:
    o.total()
total_eu(b)                            # error: expected shop::Order[Receipt = String],
                                       #        found shop::Order[Receipt = Int]
```

A method resolves on a type the caller reaches only through a run:

```python
# checkout.cambra
run shop(Receipt=String, max_order=100) as s
pub first = s::Order::placed("r-0", 42)

# deploy.cambra
run checkout as c
c::first.total()                       # 42: `deploy` neither imports nor runs `shop`
```

A module parameterized by another module, with an abstract type member:

```python
# stripe.cambra
pub Receipt = {id: Int, fee: Int}
pub def charge(amount: Int) => Receipt:
    (id=amount * 10, fee=amount // 30)
pub def fee_of(r: Receipt) => Int:
    r.fee

# billing.cambra
param payments: Module{Receipt: Type, charge: Int => Receipt, fee_of: Receipt => Int}
pub def net(amount: Int) => Int:
    amount - payments::fee_of(payments::charge(amount))

# deploy.cambra
import stripe
run billing(payments=stripe) as b
b::net(300)                            # 290; inside `billing`, `Receipt` is opaque
```

### Traits across modules (specified, not yet built)

The spec's rules ("Traits and instances across modules") need the traits stack and the modules
stack together:

```python
# shapes.cambra
pub trait Area(S):
    def area(s: S) => Int

pub type Square = Int
impl Area(Square):                     # an instance takes no `pub`: it holds wherever
    def area(s):                       # its trait and type can be named
        s.extract() * s.extract()

pub def total(C, S, xs: C) => Int requires Iterable(C, Elements=_ |=> S), Area(S):
    sum([Area::area(x) for x in xs])

# app.cambra
import shapes use Area, Square

type Circle = Int
impl Area(Circle):                     # declared in the type's module
    def area(s):
        3 * s.extract() * s.extract()

shapes::total([Square::new(2), Square::new(3)])    # 13
Area::area(Circle::new(2))                         # 12
```

- An instance is declared in its trait's module or in the module of a type its head names.
- Outside the trait's module, an instance's head has no type variable, so two modules that do
  not import each other cannot declare overlapping instances.
- **Open:** whether `shapes::total([Circle::new(1)])` may use `app`'s instance, which `shapes`
  cannot see.
