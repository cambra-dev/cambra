# Program configuration

> **Status: [Sketched].** A proposed design; nothing here is implemented. [Open
> questions](#open-questions) lists what it leaves undecided, [Out of scope](#out-of-scope) what a
> later security design decides, and [What can go wrong](#what-can-go-wrong) the failure modes other
> configuration and secret systems document.

Configuration reaches a program on sources, as data like any other. A program declares each
**configuration source** it reads, with a type the application owns, and the values live outside the
program's source. A **secret** configuration source is one whose values no inspection surface shows:
not the inspector, not the control port's replies, not an error or a log.

Configuration is not an environment variable. An environment variable belongs to a process, and a
Cambra program is not a process: an engine runs programs, reloads them in place ([docs/design.md,
"What the architecture buys"](design.md#what-the-architecture-buys)), and runs several branches of
one program at once ([program-evolution.md, "The branch
table"](../src/ccl/design/program-evolution.md#the-branch-table)). A value read once per process has
no owner in that model. A source has one: the version that declares it.

---

## Vocabulary

- **Configuration source**: a source a program declares by name, whose elements are configuration
  values of one declared type. Each element is a new version of the configuration.
- **Configuration value**: one element of a configuration source.
- **Secret configuration source**: a configuration source whose elements are `Secret(T)` values,
  which a program unwraps only by an operation that causes `Reveal` ([Secret
  configuration](#secret-configuration)).
- **Secret combinator**: `flat_map`, or a function written over it such as `map` or `map2`, which
  applies a function to the values inside secrets and returns its result as a `Secret`.
- **`Reveal`**: the effect of unwrapping a secret, which `reveal` and an append of a secret to a
  sink cause ([Revealing a secret](#revealing-a-secret)).
- **Verifier**: a function that compares a secret in constant time and reveals only the result
  ([Revealing a secret](#revealing-a-secret)).
- **Configuration payload**: the map from configuration-source name to an encoded value that a
  create or reload request carries beside the program.
- **Configuration API**: the engine endpoint that decodes a configuration payload and delivers each
  entry to the configuration source of that name. Some of what it delivers is secret.

## Configuration is a source

A configuration source is an ordinary source at the CHL layer: opening one requires
`ObserveWorld`, its elements are values, and every rule of [chl-spec.md, "7.3
Sources"](chl-spec.md#73-sources) holds.
`std::config` declares it, in the std root ([chl-spec.md, "9.16 The std
root"](chl-spec.md#916-the-std-root)). The spelling below is a sketch:

```python
import std::config

type Payments = {base_url: String, timeout_ms: Int}
type PaymentsKey = {api_key: String}

payments: Source(Payments) = config::source("payments")
payments_key: Source(Secret(PaymentsKey)) = config::secret_source("payments_key")
```

The string is the source's **name**. The type comes from the annotation, since a call does not pass
a type as an argument ([chl-spec.md, "6.10 Polymorphic types"](chl-spec.md#610-polymorphic-types)).

- **The name identifies the source.** The Configuration API delivers each entry of a payload to the
  source of the entry's name. Every declaration of one name, in any module or run, denotes one
  source, and two declarations of one name at different types are a compile error naming both. A
  module takes a source's name from a `const param`, so two runs of one module can read two sources.
- **The name is a constant**, so the engine knows every configuration source a version declares
  before the version runs, as it knows every route ([chl-spec.md, "9.19
  Constants"](chl-spec.md#919-constants)).
- **The type is the application's.** A value that does not decode at the declared type is refused at
  the Configuration API, and the refusal names the source and the field, never the value. A
  refinement on the type, `{Int where _ > 0}`, is checked at the same boundary.
- **A version starts once each configuration source it declares has a value.** A reload whose
  configuration payload leaves a declared source with no value, held or supplied, is refused, so the
  program never runs with no configuration. A declaration may name a default instead,
  `config::source_or("payments", (base_url="https://pay.example", timeout_ms=500))`.

### The `std::config` interface

Every name is a placeholder ([Open questions](#open-questions)).

| Member | Type | Does |
| --- | --- | --- |
| `source(name)` | `String => Source(T)` | Declares the configuration source `name`, whose elements are `T` |
| `secret_source(name)` | `String => Source(Secret(T))` | Declares the secret configuration source `name` |
| `source_or(name, default)` | `{String, T} => Source(T)` | Declares `name` with `default` as its value until one is supplied |
| `first(s)` | `Source(T) => T` | The value `s` holds when the version starts, which a mutable variable's declaration takes as its initial value |
| `Secret(T)` | nominal builtin | Holds a value that only an operation causing `Reveal` unwraps |
| `secret(v)` | `@Builtin`, `T => Secret(T)` | Wraps `v` as a `Secret` |
| `s.flat_map(f)` | `@Builtin`, `{Secret(T), (T => Secret(U) requires Context)} => Secret(U)` | Applies `f` to the value `s` holds |
| `reveal(s)` | `@Builtin`, `Secret(T) => T causes Reveal` | The value `s` holds |
| `s.map(f)` | `{Secret(T), (T => U requires Context)} => Secret(U)` | `s.flat_map(lambda x: secret(f(x)))` |
| `s.map2(t, f)` | `{Secret(T), Secret(U), ({T, U} => V requires Context)} => Secret(V)` | `s.flat_map(lambda x: t.map(lambda y: f(x, y)))` |
| `sequence(xs)` | `List(Secret(T)) => Secret(List(T))` | A fold of `xs` over `map2` |
| `secret_eq(s, guess)` | `{Secret(T), T} => Bool requires Equatable(T, T) causes Reveal` | `reveal(s.map(lambda v: constant_time_eq(v, guess)))` |
| `hmac_verify(key, msg, sig)` | `{Secret(String), String, String} => Bool causes Reveal` | `reveal(key.map(lambda k: constant_time_eq(hmac_sha256(k, msg), sig)))` |

Opening a source requires `ObserveWorld`. The engine knows every configuration source before the
version runs, so `source`, `secret_source` and `source_or` are called only as the whole right-hand
side of a top-level `=`, as `http_serve` is ([chl-spec.md, "7.3 Sources"](chl-spec.md#73-sources)).
`T` is a type parameter inferred from the annotation or from `default`.

### Reading the latest value

A use reads the configuration as of its own position. The program folds the source into a
transactional mutable variable, and a use inside a request loop's transaction reads that variable as
of the transaction's commit position ([chl-spec.md, "8.3 Reads"](chl-spec.md#83-reads)), which
compiles to the `as_of` temporal join (`Builtin::AsOf`):

```python
settings: Mut(Payments, Txn) := config::first(payments)
for p in payments:
    with begin():
        settings := p

for req in charges:
    with begin():
        url = settings.base_url      # the value as of this transaction's commit
```

A function cannot package the fold, since a `Mut` is never returned ([chl-spec.md, "8.1 Mutation is
explicit: the `:=` operator"](chl-spec.md#81-mutation-is-explicit-the--operator)).

- **A configuration change never reruns a use.** The as-of read samples the variable at the reader's
  commit position, so a request handled before a change keeps the value it read.
- **Values read in one block are one snapshot.** A block that reads two configuration variables
  reads both at one commit position. Values that must change together, a key and its certificate,
  are one configuration value rather than two sources, since a block that reads the two sources'
  latest values at different positions pairs a new key with an old certificate.
- **A configuration source that receives nothing does not stall its readers.** An as-of read waits
  for the frontier of the variable it reads, and a variable with no outstanding commit has its
  frontier at the reader's position. This needs a test before it is relied on: an event-time
  temporal join in Flink waits on both inputs' watermarks, and a table that rarely changes stalls
  it.

### Branches

A branch shares a configuration source with its parent when both read the same source, as it shares
any source ([program-evolution.md, "Every branch reads every
element"](../src/ccl/design/program-evolution.md#every-branch-reads-every-element)). A branch that
wants its own configuration declares another configuration source,
`config::secret_source("payments_key_staging")`, and the Configuration API delivers to it by that
name.

## Secret configuration

A secret configuration source's elements have type **`Secret(T)`**, a nominal builtin as `Set` and
`Map` are ([chl-spec.md, "Collection operations"](chl-spec.md#collection-operations)). A builtin
has no constructors and no `extract`. `secret(v)` builds a `Secret`. A program stores a `Secret`,
passes it, and folds it into a mutable variable. It computes on the value inside through the
**secret combinators**, whose results are `Secret` values again. `flat_map` is the one `@Builtin`
combinator, and `map`, `map2` and `sequence` are ordinary polymorphic functions that `std::config`
writes over it ([The `std::config` interface](#the-stdconfig-interface)). Two operations unwrap a
`Secret`, `reveal` and an append to a sink, and each causes the effect `Reveal` ([Revealing a
secret](#revealing-a-secret)). The spelling below is a placeholder:

```python
key: Mut(Secret(PaymentsKey), Txn) := config::first(payments_key)
for k in payments_key:
    with begin():
        key := k

for req in charges:
    with begin():
        auth = key.map(lambda k: "Bearer " + k.api_key)    # Secret(String)
        payments_api << (auth=auth, body=req)
```

`payments_api` is a sink for outbound requests, which is not designed yet. Its element type is
`{auth: String, body: Charge}`, and the append puts a `Secret(String)` at `auth`. The sink unwraps
it as it encodes the request, so the append causes `Reveal`, and the inspector shows each request's
`body` and redacts its `auth`.

`map2` combines two secrets into one, as a key and its certificate combine into one TLS identity:
`cert.map2(pkey, lambda c, k: (cert=c, key=k))`. `sequence` combines a list of secrets. A program
combines more secrets by nesting `flat_map` once per secret, since CHL has no type over tuples of
every length to give an N-ary combinator. `flat_map` also chooses a secret by the value of another
secret, which no fixed-arity combinator does.

### Confinement is typing

No value computed from a secret leaves a `Secret` except through an operation that causes
`Reveal`. Existing type rules check this, and none of them is particular to secrets:

- **A `Secret(T)` is not a `T`.** Subtyping relates a nominal type only to itself and its
  refinements ([chl-spec.md, "A nominal type is opaque"](chl-spec.md#a-nominal-type-is-opaque)), so
  a `Secret(String)` passed where a `String` is expected is a type error. The one exception is an
  element appended to a feed that a sink consumes, and that append causes `Reveal`.
- **The function a combinator applies causes nothing.** `flat_map`'s parameter type,
  `(T => Secret(U) requires Context)`, has no `causes` clause, and a written type's clauses are
  exact ([chl-spec.md, "Writing requirements and
  effects"](chl-spec.md#writing-requirements-and-effects)). A function that appends to a feed,
  writes a variable or raises is refused at the call. Its result is its one output, and that result
  is a `Secret`. The function may require anything, since a requirement is an input. `map`, `map2`
  and `sequence` call their functions inside a function they pass to `flat_map`, and their written
  parameter types state the same bound.
- **`Secret` has no `Equatable` or `Orderable` instance.** `==` on a `Secret`, and a `Secret` as
  the key of a `Set`, a `Map` or a `groupby`, are type errors ([chl-spec.md, "Equality and
  order"](chl-spec.md#equality-and-order)).
- **A condition on a secret is decided inside a combinator, so a selection is a `Secret` too.**
  `allowed.map(lambda ids: [u for u in users if u.id in ids])` is a `Secret(List(User))`. A
  transactional mutable variable that holds it has a `Secret` type, so a selection that one
  transaction stores and another reads stays secret.

Both appends below are compile errors:

```python
leaked: Feed(String)
for req in charges:
    with begin():
        leaked << key.map(lambda k: k.api_key)    # a Secret(String) is not a String, and no
                                                  # sink consumes leaked
        key.map(lambda k: leaked << k.api_key)    # the function causes Append(leaked)
```

### Redaction

The inspector, the control port's replies, errors and the engine's logs redact every
`Secret`-typed value. They also redact every term evaluated inside a function that `flat_map`
applies, including the terms of each function it calls, so the functions `map` and `map2` apply
are covered. Every call is resolved when the
program is compiled ([chl-spec.md, "Inputs from outside the
program"](chl-spec.md#inputs-from-outside-the-program)), so the redacted terms are fixed before the
program runs. Redaction is decided from types and call paths, never by matching a value's text,
which GitHub Actions does and which misses an encoded or reformatted copy ([Security
hardening](https://docs.github.com/en/actions/security-for-github-actions/security-guides/security-hardening-for-github-actions)).
The inspector shows a redacted value as a marker. A value `reveal` returns is not a `Secret`, and
the inspector shows it.

### Revealing a secret

`Reveal` is an effect, and no construct discharges it, as none discharges `AffectWorld`
([chl-spec.md, "Discharging requirements and
effects"](chl-spec.md#discharging-requirements-and-effects)). Two operations cause it:

- **`reveal(s)` returns the value `s` holds.** A function that calls `reveal`, directly or through
  a call, has `Reveal` in its `causes` clause, and `cambra check` prints it ([chl-spec.md, "9.14
  Checking a module on its own"](chl-spec.md#914-checking-a-module-on-its-own)). The function a
  combinator applies causes nothing, so it cannot reveal.
- **A sink unwraps a `Secret` at any position.** A value appended to a feed that a sink consumes
  may hold a `Secret(T)` at any position where the feed's element type has a `T`. The sink unwraps
  each one as it encodes the element, and the append causes `Reveal`. A sink names no positions,
  so a client whose protocol takes a key in a header, a query parameter or a body field takes it
  there. A sink that unwraps a value manages it, its error text included.

```python
calls << (method="POST", url=base_url + "/charges",
          headers=map([("X-Api-Key", key)]),       # key: Secret(String) where a String goes
          body=json::encode(c))
```

Up to the append, the element holds the `Secret`, so the inspector shows the method, the URL and the
body, and redacts the key.

A **verifier** compares a secret in constant time and reveals only the result. `secret_eq` and
`hmac_verify` are library functions over `reveal` ([The `std::config`
interface](#the-stdconfig-interface)), so their types say `causes Reveal`. A webhook checks its
signature before it acts on a request, and a login checks a stored password hash with
`secret_eq(stored, argon2id(given, salt))`:

```python
hook_key: Mut(Secret(String), Txn) := config::first(hook_secret)   # folded as above

for r in hooks:
    with begin():
        if config::hmac_verify(hook_key, r.body, r.sig):
            events << parse(r.body)
```

`hooks` stands for a source whose elements carry a body and a signature. A verifier bounds what one
call reveals, not what many calls reveal: a low-entropy secret, such as a PIN, is recovered through
`secret_eq` by trying every candidate, and limiting attempts is the program's job.

**A function type bounds `Reveal`.** A written function type's clauses are exact, so a parameter
`handler: (Request => Response causes Effect except Reveal)`, or one typed with a clause variable
`E <: Effect except Reveal`, accepts only a function that reveals nothing ([chl-spec.md, "Kinds and
bounds"](chl-spec.md#kinds-and-bounds)). A Module type's entry bounds a run's member the same way.
A `def` states the bound as `causes only Effect except Reveal`, which also puts every other effect
in its contract. That clause holds the top `WriteTxn(*)`, so every call counts as writing every
transactional variable, for transaction footprints and `await_final`. A clause that infers the
body's effects less one capability is a dependency ([Dependencies](#dependencies)).

## Where configuration comes from

A configuration value reaches a program from one of three places: the request that creates or
reloads a version, a remote keystore the program calls, or a local file on the engine's host. CI is
one producer of the first. A proxy or other deploy-time service may build the same request, adding
the payload's secret values to the program.

### The create or reload request

The configuration payload travels with the program, in the control port request that creates a
branch or reloads one ([program-evolution.md, "The control
port"](../src/ccl/design/program-evolution.md#the-control-port)). The `cambra` CLI is one client of
it, and its commands are placeholders:

| Command | Does |
| --- | --- |
| `cambra reload [--branch b] [--config FILE] [--config-env PREFIX] PROGRAM` | Sends the program and a configuration payload to `/reload` as one request |
| `cambra branch NAME [--from p] [--config FILE] PROGRAM` | Sends the program and a configuration payload to `/branch/<name>` as one request |
| `cambra config set [--branch b] NAME [FILE]` | Sends one configuration value to a running version, with no reload |
| `cambra config list [--branch b]` | Lists each configuration source the version declares, whether it holds a value, and for a secret an HMAC of the value |

- **A version and its configuration are installed as one step.** The engine compiles the version,
  decodes the payload against the version's declared types, checks that every declared source has a
  value, and installs the version with its configuration. The new version processes no element
  before its configuration arrives. A refused request changes nothing, as a refused reload does
  today.
- **A value set without a reload is a new element.** `config set` appends to the source, and every
  reader sees it at its next position.
- **A payload that omits a source keeps the value it holds.** Removing a value is explicit, `cambra
  config unset NAME`, and is refused while a running version declares the source with no default.
- **The CLI reads values from files, standard input, or its environment.** `--config-env PREFIX`
  sends each environment variable named `PREFIX_<NAME>` as the value of `<NAME>`. A value never
  appears on the command line, which shell history and `/proc/<pid>/cmdline` keep. Whatever builds
  the payload holds the secrets in it.
- **Nothing returns a secret value.** No endpoint reads a secret back. `config list` shows an
  HMAC-SHA256 of each secret under a key the engine holds, as Vault's audit log does ([Audit
  devices](https://developer.hashicorp.com/vault/docs/audit)), so an operator can tell whether a
  value changed or two sources hold the same value. A plain hash would not do: a low-entropy secret,
  such as a PIN or a short password, is recovered from its SHA-256 by trying every candidate, and
  the HMAC's key is what an attacker lacks.

Design work that remains:

- **The request's wire shape [Open]**: how a value is encoded against its declared type, and how the
  payload and a bundle of several modules share one request ([docs/modules.md, "Program
  evolution"](modules.md#program-evolution)).
- **Delivery to a shared source.** A branch shares a source with its parent when both read it
  ([Branches](#branches)), so a value a branch's request supplies for a shared source reaches the
  parent too. Either the request is refused, or it is delivered to every branch reading the source.

**Reload delivers a version's configuration before the version's first tick.** A configuration
source is a host-registered source the control port feeds, and a reload today installs a version
with no step that feeds a source before the version runs ([program-evolution.md, "How a reload
works"](../src/ccl/design/program-evolution.md#how-a-reload-works)). This is a requirement on
`LiveProgram`'s reload path.

### Remote keystores

A remote keystore is a (sink, source) pair, as `http_serve` is a (source, sink) pair: the program
feeds requests to the sink and reads the keystore's replies from the source. A request carries a
secret, such as a Vault token, as a `Secret` at the position the keystore expects it, and the sink
unwraps it ([Revealing a secret](#revealing-a-secret)). The source decodes each reply at its
declared type and wraps each position the type marks `Secret`, as the Configuration API does. A
reply typed `{token: Secret(String), expires_at: time::Instant}` lets a program schedule its next
refresh from `expires_at` without unwrapping the token. Nothing else about a keystore is
particular to configuration.

Vault is one instance. A credential with a short lease is refreshed on a timer, `time::alarms()`:
each alarm feeds a request carrying the token, and each reply is folded into a transactional mutable
variable that uses read as of their positions. A request per use would put one lease per use on the
keystore.

Design work that remains:

- **Outbound pairs.** No source and sink pair for calls made outside the program exists yet.
- **Startup.** A fetched credential is a mutable variable, not a configuration source, so the rule
  that a version starts once each source has a value does not cover it. The program needs a value to
  start from, or a way to hold its requests until the first reply arrives.
- **An unreachable keystore.** The variable keeps its last value, and the program decides when a
  value is too old to use.

### Local files [Open]

The engine reads a file on its host, such as a Kubernetes Secret mounted as a volume or a file a
Vault Agent renders, and delivers its contents to a configuration source, with a new element each
time the file changes. Undecided: whether the program or the engine's deployment names the path,
since a path in the program ties it to one host; how a change is detected; and what a deleted or
unreadable file does to the source.

## Secret values at rest [Open]

Where an engine may keep a secret value is undecided, because durable state is
[Sketched](design.md#feature-status-at-a-glance). What has to be decided:

- **Source history keeps old values.** A source's elements stay until every reader releases them
  ([program-evolution.md, "The release
  model"](../src/ccl/design/program-evolution.md#the-release-model)). A configuration source whose
  one reader is the fold above releases every value before the latest, so the engine holds one value
  per source. This is a conjecture until the fold is checked to release.
- **State built from a secret is a secret.** A stored outbound request that carries a key holds the
  key, and a reload carries that state forward.
- **A branch copies its parent's state**, secrets included ([program-evolution.md, "A branch is
  created by
  branch-and-reload"](../src/ccl/design/program-evolution.md#a-branch-is-created-by-branch-and-reload)).
- **The candidates:** memory only, with every secret supplied again after a restart; encrypted at
  rest under a key the engine holds; or one key per value, destroyed to erase the value.

## What can go wrong

Each item is a failure documented in another system, how it applies here, and what this design does
about it.

### Secrets persist in plaintext

Terraform's `sensitive` changes display only, and the value stays in state and plan files ([Manage
sensitive data](https://developer.hashicorp.com/terraform/language/manage-sensitive-data)). Helm
keeps every release's values, so its revision history is a secret store. Kubernetes encrypts an
existing Secret only when it is next written ([Encrypting data at
rest](https://kubernetes.io/docs/tasks/administer-cluster/encrypt-data/)). Here: an engine that
records the configuration of each version, for `/branch/<name>/info` or a rollback, records HMACs,
never values. A source that a later version marks secret leaves its earlier history unmarked until
it is rewritten. [Secret values at rest [Open]](#secret-values-at-rest-open) covers the rest.

### Code and configuration are applied out of order

Erlang/OTP calls `config_change/3` after the new code is loaded, so new code runs with old
configuration for a moment, and a failed release upgrade restarts on the old release instead of
undoing its steps ([Release handling](https://www.erlang.org/doc/system/release_handling.html)).
Here: the reload installs the version and its configuration in one step, and a version starts only
once each source it declares has a value.

### A reader starts before any value arrives

Flink evaluates events that arrive before the broadcast rules against empty state ([Broadcast
state](https://nightlies.apache.org/flink/flink-docs-stable/docs/dev/datastream/fault-tolerance/broadcast_state/)).
Envoy holds initialization until its first configuration arrives, then falls back to a cached value
([xDS protocol](https://www.envoyproxy.io/docs/envoy/latest/api-docs/xds_protocol)). Here: the
reload refuses a version that would start with a declared source empty and no default.

### Short-lived credentials cannot wait for a reload

Projected Kubernetes ServiceAccount tokens last an hour, and enough clients failed to reread them
that the KEP added a mode extending them to a year
([KEP-1205](https://github.com/kubernetes/enhancements/blob/master/keps/sig-auth/1205-bound-service-account-tokens/README.md)).
Here: `cambra config set` delivers between reloads, and a program refreshes a leased credential
itself ([Remote keystores](#remote-keystores)).

### The configuration type changes across a reload

A reload that changes a configuration source's type holds a value at the old type. The value is
state, and [program-evolution.md, "State
takeover"](../src/ccl/design/program-evolution.md#state-takeover) refuses a value that does not fit
its new declaration, so the reload must carry a new value or a conversion.

### Valid configuration can still be wrong

Envoy rejects a configuration it cannot apply, keeps the last one it accepted, and reports the
rejected version to the server. Here: a value that fails its type or refinement is refused at the
Configuration API and the source keeps its last value. A well-typed value that is wrong, an expired
key, is the application's to detect.

## Open questions

- **Rotation.** A use reads its key as of its commit position, and an outbound request built there
  may leave after a rotation, so the upstream service has to accept the old key until requests built
  with it have drained. AWS's alternating-users rotation keeps the previous credential valid for
  this reason ([Rotation
  strategies](https://docs.aws.amazon.com/secretsmanager/latest/userguide/rotation-strategy.html)).
  The first implementation cuts over: a new value replaces the old at one position, and a request
  built before it carries the old key.
- **Where secret values live at rest** ([Secret values at rest
  [Open]](#secret-values-at-rest-open)).
- **Local files** ([Local files [Open]](#local-files-open)).
- **Values computed from a secret that are not secret.** Ciphertext and a signature are computed
  from a key and are meant to leave as plain values. `reveal(key.map(lambda k: aes_gcm(k, nonce,
  pt)))` expresses each one as a `Reveal`. Whether an operation can state that its result is not
  secret, so that it causes no `Reveal`, is undecided.
- **Redacting part of a string.** A secret formatted into a string, such as a query string
  `?key=…&q=1`, makes the whole string a `Secret`, and the inspector redacts all of it. A format
  combinator whose result keeps its plain segments visible would redact only the secret ones.
- **Combining secrets without nesting.** Combining N secrets nests `flat_map` N deep. A second
  `@Builtin` combinator, `using(f)`, would combine any number at one depth. It calls `f` once,
  passing it a function that unwraps any secret, and returns `f`'s result as a `Secret`:
  `using(lambda unwrap: unwrap(a) + unwrap(b) + unwrap(c))` is a `Secret`. `using` computes nothing
  that nested `flat_map` does not: inside the innermost function of
  `a.flat_map(lambda x: b.flat_map(lambda y: …))`, `x` and `y` are plain values, as `unwrap(a)` and
  `unwrap(b)` are. It removes the nesting and nothing else. The unwrapping function
  exists only as `f`'s argument. `f` causes nothing, so it cannot store the function, and the
  function leaves `f` only inside the `Secret` that `using` returns. `using`'s type is
  `((forall (T) Secret(T) => T) => U requires Context) => Secret(U)`: its argument is a function
  that takes a polymorphic argument, which is **[Open]** and an error ([chl-spec.md, "Polymorphic
  type annotations"](chl-spec.md#polymorphic-type-annotations)). `using` waits on that rule.
- **Computing on a secret without a lambda.** Every computation on a secret is a function passed to
  a combinator. A type that names a scope, `In(s, T)` for a value computed under
  `with secrets() as s:`, would let ordinary operators apply to a secret, with the compiler lifting
  each one as `map` does. The cost is inference that is polymorphic over scope labels, and tracking
  of implicit flows: a branch on a labeled value labels every effect inside the branch.
- **Names.** Every name in this document's examples is a placeholder until the design settles:
  `std::config` and its functions, `Secret`, `secret`, `reveal`, `Reveal`, the combinators, the
  verifiers, and the CLI's commands.

## Out of scope

These belong to a security design that comes later:

- **Who may reload a program, create a branch, set a secret, or ship a module that causes
  `Reveal`.**
  Whoever can reload a program can ship one that sends every secret it holds to a sink, as anyone
  who can create a Kubernetes Pod can read the Secrets it mounts ([Secrets good
  practices](https://kubernetes.io/docs/concepts/security/secrets-good-practices/)). Role-based
  access and policy controls, such as a policy naming the modules that may cause `Reveal`, answer
  it. A module's top level has no `causes` clause, so nothing in the language bounds what a whole
  module reveals.
- **Authenticating to the control port.** It has none today. It binds loopback
  (`src/control_port.rs`), so every process on the engine's host reaches it.
- **Idempotent control port requests.** A create or reload request sent twice appends its
  configuration values twice. An idempotency key on each request is a requirement on the control
  API's design, which has no document yet; the verbs it covers are [program-evolution.md, "The
  control port"](../src/ccl/design/program-evolution.md#the-control-port).
- **How a program authenticates to a remote keystore**, such as short-lived signed tokens bound to
  an audience and a program, as Kubernetes ServiceAccount tokens are.

## Dependencies

- `Secret` as a nominal builtin, and `secret`, `flat_map` and `reveal` as `@Builtin` functions of
  `std::config` ([chl-spec.md, "9.16 The std root"](chl-spec.md#916-the-std-root)).
- `Reveal` as an effect in the table of [chl-spec.md, "6.9
  Capabilities"](chl-spec.md#69-capabilities), discharged by no construct, as `AffectWorld` is not.
- A `causes` clause that infers a `def`'s effects less one capability, such as
  `causes only _ except Reveal`. `causes only Effect except Reveal` excludes `Reveal` but claims
  every other effect. `except RunTransaction` needs the same form, for a function that must not
  commit.
- A feed type that states a sink consumes the feed, and typing for an element that holds a
  `Secret(T)` at a position of type `T`. A collection literal that mixes `T` and `Secret(T)`, such
  as a header map with one secret value, has no join today ([chl-spec.md, "A nominal type is
  opaque"](chl-spec.md#a-nominal-type-is-opaque)).
- The std root ([chl-spec.md, "9.16 The std root"](chl-spec.md#916-the-std-root)), which holds
  `std::config`.
- An outbound (sink, source) pair, for remote keystores.
- A reload of a program of several modules ([docs/modules.md, "Program
  evolution"](modules.md#program-evolution)), since `std::config` is a module.
- Durable state, for [Secret values at rest [Open]](#secret-values-at-rest-open).
