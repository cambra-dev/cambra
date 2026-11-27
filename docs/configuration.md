# Program configuration

> **Status: [Sketched].** A proposed design; nothing here is implemented. [Open
> questions](#open-questions) lists what it leaves undecided, [Out of scope](#out-of-scope) what a
> later security design decides, and [What can go wrong](#what-can-go-wrong) the failure modes other
> configuration and secret systems document.

Configuration reaches a program as **settings**. A setting is a run of the std module
`config::setting`, and its run path names it. The value lives outside the program's source, and
the request that creates or reloads a version carries it. A **secret** setting is one whose type is
`Secret(T)`, and no inspection surface shows its value: not the inspector, not the control port's
replies, not outbound telemetry, not an error or a log.

Configuration is not an environment variable. An environment variable belongs to a process, and a
Cambra program is not a process: an engine runs programs, reloads them in place ([docs/design.md,
"What the architecture buys"](design.md#what-the-architecture-buys)), and runs several branches of
one program at once ([program-evolution.md, "The branch
table"](../src/ccl/design/program-evolution.md#the-branch-table)). A value read once per process has
no owner in that model. A setting has one: the run that holds it.

---

## Vocabulary

- **Setting**: a run of `config::setting` or `config::setting_or`. It holds one configuration
  value of its declared type in a cell, and a program reads the value with the run's `get`.
- **Setting path**: a setting's run path, such as `payments` or `eu::stripe_key`. The payload, the
  CLI and every refusal name a setting by its path.
- **Secret setting**: a setting whose type is `Secret(T)`. A program unwraps its value only by
  calling `reveal` ([Secret configuration](#secret-configuration)).
- **Secret combinator**: `flat_map`, or a function written over it such as `map` or `map2`, which
  applies a function to the values inside secrets and returns its result as a `Secret`.
- **Verifier**: a function that compares a secret in constant time and reveals only the result
  ([Revealing a secret](#revealing-a-secret)).
- **Configuration payload**: the map from setting path to an encoded value that a create or reload
  request carries beside the program.
- **Configuration API**: the engine endpoint that decodes a configuration payload and delivers each
  entry to the setting at that path. Some of what it delivers is secret.

## A setting is a run

A program runs `config::setting` once per setting, with the setting's type as the argument `T`
([chl-spec.md, "9.3 Runs"](chl-spec.md#93-runs)). `std::config` is in the std root ([chl-spec.md,
"9.16 The std root"](chl-spec.md#916-the-std-root)). The spelling below is a sketch:

```python
import std::config

type Payments = {base_url: String, timeout_ms: Int}
type PaymentsKey = {api_key: String}

run config::setting(T=Payments) as payments
run config::setting(T=Secret(PaymentsKey)) as payments_key

for c in charges:
    with begin():
        p = payments::get()          # Payments, as of this transaction
        k = payments_key::get()      # Secret(PaymentsKey)
```

`config::setting` is an ordinary module. It holds the source, the cell and the fold, and exports
the source and a function that reads the cell:

```python
param T

pub updates: Source(T) = __config_source()   # @Builtin, fed by the Configuration API
value: Cell(T) := first(updates)
for v in updates:
    with begin():
        value := v

pub def get() => T: value
```

- **The run path names the setting.** `__config_source()` takes its key from the path of the run
  that calls it, so `run config::setting(T=Payments) as payments` reads the payload entry
  `payments`. The `as` name is the setting's name. A setting inside a library's run `eu` that the
  library names `stripe_key` has the path `eu::stripe_key`.
- **Every run is its own setting.** Two runs of `config::setting` are two settings, as two runs of
  any module are two runs ([chl-spec.md, "9.3 Runs"](chl-spec.md#93-runs)). A library that needs
  configuration runs `config::setting` itself. Code that shares a setting receives the run as an
  argument, and no module reads a setting by naming its path.
- **The path follows the program's structure.** Renaming a run or moving it into another run
  changes its path. A reload marks the move with `@RenamedFrom` ([Held values, renames and
  removal](#held-values-renames-and-removal)), and the payload uses the new path. A library's
  settings are named by the run the caller gives the library.
- **The engine knows every setting before the version runs**, since every run is resolved when the
  program is compiled. `cambra config list` prints the version's settings by path and type.
- **The type is the application's.** A value that does not decode at `T` is refused at the
  Configuration API, and the refusal names the setting's path and the field, never the value. A
  refinement on the type, `{Int where _ > 0}`, is checked at the same boundary.
- **A setting is secret when its `T` is `Secret(…)`.** The engine decides from `T` which values
  `config list` shows as an HMAC and which refusals omit field values. A setting needs no other
  declaration to be secret.

### The first value

`first(updates)` is the value of the source's first element. A read of a cell whose initial value
is not ready waits for it, and nothing else in the program waits:

- **A new run**, from a create or from a reload that adds the run, evaluates its initializer
  ([chl-spec.md, "9.18 Reloading a program of
  modules"](chl-spec.md#918-reloading-a-program-of-modules)). The engine appends the payload's entry
  for the setting as element 0 while it installs the version, so no reader waits.
- **A run the reload keeps** takes over its state, and its initializer is not evaluated. A value
  for it in the payload is an ordinary update.
- **A setting with no value**, such as a local run with no payload, has readers that wait until
  `config set` supplies one. The rest of the program runs.

A create or reload request that leaves a new setting with no value and no default is refused
([The create or reload request](#the-create-or-reload-request)). `first` crosses from a source into
a cell, which [mutability-model.md, "Crossing between dataflow and
transactions"](../src/ccl/design/mutability-model.md#crossing-between-dataflow-and-transactions)
does not yet list, so it needs a rule in the spec ([Dependencies](#dependencies)).

### The `std::config` interface

Every name is a placeholder ([Open questions](#open-questions)).

| Member | Type | Does |
| --- | --- | --- |
| `setting(T)` | module, `param T` | A setting of type `T`, whose path is the run's path |
| `setting_or(default)` | module, `param default: T` | A setting whose initial value is `default` until the Configuration API supplies one |
| `r::get()` | `() => T`, a member of a run `r` | The setting's value as of the calling transaction |
| `r::updates` | `Source(T)`, a member of a run `r` | Each value the Configuration API delivers |
| `Secret(T)` | nominal builtin, covariant in `T` | Holds a value that only `reveal` unwraps |
| `secret(v)` | `@Builtin`, `T => Secret(T)` | Wraps `v` as a `Secret` |
| `s.flat_map(f)` | `@Builtin`, `{Secret(T), (T => Secret(U) requires Context except ReadTxn(*))} => Secret(U)` | Applies `f` to the value `s` holds |
| `reveal(s)` | `@Builtin`, `Secret(T) => T` | The value `s` holds |
| `s.map(f)` | `{Secret(T), (T => U requires Context except ReadTxn(*))} => Secret(U)` | `s.flat_map(\x -> secret(f(x)))` |
| `s.map2(t, f)` | `{Secret(T), Secret(U), ({T, U} => V requires Context except ReadTxn(*))} => Secret(V)` | `s.flat_map(\x -> t.map(\y -> f(x, y)))` |
| `sequence(xs)` | `List(Secret(T)) => Secret(List(T))` | A fold of `xs` over `map2` |
| `secret_eq(s, guess)` | `{Secret(T), T} => Bool requires Equatable(T, T)` | `reveal(s.map(\v -> constant_time_eq(v, guess)))` |
| `hmac_verify(key, msg, sig)` | `{Secret(String), String, String} => Bool` | `reveal(key.map(\k -> constant_time_eq(hmac_sha256(k, msg), sig)))` |

`setting_or` takes `T` from `default`, which needs the **[Planned]** inference of an argument left
out ([chl-spec.md, "9.4 Parameters"](chl-spec.md#94-parameters)). Until then a run passes both:
`run config::setting_or(T=Payments, default=(base_url="https://pay.example", timeout_ms=500)) as
payments`. `Secret` is read-only, so a `Secret(T)` is a `Secret(U)` whenever `T` is a subtype of
`U`, as the stated variances of `Set` and `Map` are ([chl-spec.md, "Collection
operations"](chl-spec.md#collection-operations)).

### Reading the latest value

A program reads a setting with `get()` inside a transaction, which reads the setting's cell as of
that transaction ([mutability-model.md, "Cells"](../src/ccl/design/mutability-model.md#cells)):

```python
for req in charges:
    with begin():
        url = payments::get().base_url      # the value as of this transaction
```

- **A configuration change never reruns a use.** A request handled before a change keeps the value
  it read.
- **Values read in one transaction are one snapshot.** Transactions are serializable, so two
  settings read in one transaction are read at one point in the commit order.
- **Values that must change together are one setting.** A key and its certificate are one value,
  since two `config set` calls commit two updates, and a transaction between them reads a new key
  with an old certificate.

### Branches

A setting is shared by every branch that runs it. A branch copies its parent's state, so a new
branch starts with its parent's values. The Configuration API feeds each setting's source once,
and every branch reads every element of it, as of any source ([program-evolution.md, "Every branch
reads every element"](../src/ccl/design/program-evolution.md#every-branch-reads-every-element)), so
each branch's copy of the run applies every later value. A branch that wants its own value runs
another setting, `run config::setting(T=Secret(PaymentsKey)) as payments_key_staging`, so the
difference between the branches is in their source.

## Secret configuration

A secret setting's value has type **`Secret(T)`**, a nominal builtin as `Set` and `Map` are
([chl-spec.md, "Collection operations"](chl-spec.md#collection-operations)). A builtin has no
constructors and no `extract`. `secret(v)` builds a `Secret`. A program stores a `Secret`, passes
it, and holds it in a cell. It computes on the value inside through the **secret combinators**,
whose results are `Secret` values again. `flat_map` is the one `@Builtin` combinator, and `map`,
`map2` and `sequence` are ordinary polymorphic functions that `std::config` writes over it ([The
`std::config` interface](#the-stdconfig-interface)). `reveal` is the one operation that unwraps a
`Secret` ([Revealing a secret](#revealing-a-secret)). The spelling below is a placeholder:

```python
for req in charges:
    with begin():
        auth = payments_key::get().map(\k -> "Bearer " + k.api_key)    # Secret(String)
        calls << (method="POST", url=base_url + "/charges",
                  headers=map([("Authorization", http::hidden(auth))]),
                  body=http::plain(json::encode(req)))
```

`calls` is the collection an HTTP client sink takes, which is not designed yet. Its header values
and its body are each a `String` or a `Secret(String)`, which the sink's parameter type states as
a sum, spelled here `http::plain` and `http::hidden`. The sink writes a hidden value's bytes to the
request. The inspector and outbound telemetry show the method, the URL and the body, and redact
the `Authorization` header.

A body that contains a secret is built inside a combinator, `key.map(\k -> json::encode(…))`, and
is redacted whole. Redacting one field needs a structured body whose `Secret` leaves the sink
encodes itself ([Open questions](#open-questions)).

`map2` combines two secrets into one, as a key and its certificate combine into one TLS identity:
`cert.map2(pkey, \c, k -> (cert=c, key=k))`. `sequence` combines a list of secrets. A program
combines more secrets by nesting `flat_map` once per secret, since CHL has no type over tuples of
every length to give an N-ary combinator. `flat_map` also chooses a secret by the value of another
secret, which no fixed-arity combinator does.

### Confinement is typing

No value computed from a secret leaves a `Secret` except through `reveal`. Existing type rules
check this, and none of them is particular to secrets:

- **A `Secret(T)` is not a `T`.** Subtyping relates a nominal type only to itself and its
  refinements ([chl-spec.md, "A nominal type is opaque"](chl-spec.md#a-nominal-type-is-opaque)), so
  a `Secret(String)` passed where a `String` is expected is a type error. There is no implicit
  conversion from one to the other ([chl-spec.md, "8.7 Transactions as contextual
  parameters"](chl-spec.md#87-transactions-as-contextual-parameters)). A sink that accepts a secret
  states it in its parameter type.
- **The function a combinator applies causes nothing.** `flat_map`'s parameter type has no `causes`
  clause, and a written type's clauses are exact ([chl-spec.md, "Writing requirements and
  effects"](chl-spec.md#writing-requirements-and-effects)). A function that appends to a feed,
  writes a cell or raises is refused at the call. Its result is its one output, and that result is
  a `Secret`. `map`, `map2` and `sequence` call their functions inside a function they pass to
  `flat_map`, and their written parameter types state the same bound.
- **The function a combinator applies reads no cell.** Its requirements are `Context except
  ReadTxn(*)`, which becomes `Context except ReadCell(*)` under [mutability-model.md, "Footprints
  and elision"](../src/ccl/design/mutability-model.md#footprints-and-elision). A transaction's
  footprint names each place it reads, per path. A read of `limits[k]` inside `key.map(\k ->
  limits[k])` would put the key into the footprint, `limits["sk_live_…"]`, and no redaction covers
  footprints. A program reads a cell before the combinator and captures the value.
- **`Secret` has no `Equatable` or `Orderable` instance.** `==` on a `Secret`, and a `Secret` as
  the key of a `Set`, a `Map` or a `groupby`, are type errors ([chl-spec.md, "Equality and
  order"](chl-spec.md#equality-and-order)).
- **A condition on a secret is decided inside a combinator, so a selection is a `Secret` too.**
  `us = users` followed by `allowed.map(\ids -> [u for u in us if u.id in ids])` is a
  `Secret(List(User))`. The transaction's footprint is all of `users`, whatever the secret holds. A
  cell that holds the selection has a `Secret` type, so a selection that one transaction stores and
  another reads stays secret.

Both appends below are compile errors:

```python
leaked: Feed(String)
for req in charges:
    with begin():
        k = payments_key::get()
        leaked << k.map(\k -> k.api_key)     # a Secret(String) is not a String
        k.map(\k -> leaked << k.api_key)     # the function causes Append(leaked)
```

### Redaction

The inspector, the control port's replies, outbound telemetry, errors and the engine's logs redact
every `Secret`-typed value. They also redact every term evaluated inside a function that `flat_map`
applies, including the terms of each function it calls, so the functions `map` and `map2` apply
are covered. Every call is resolved when the program is compiled ([chl-spec.md, "Inputs from
outside the program"](chl-spec.md#inputs-from-outside-the-program)), so the redacted terms are
fixed before the program runs. Redaction is decided from types and call paths, never by matching a
value's text, which GitHub Actions does and which misses an encoded or reformatted copy ([Security
hardening](https://docs.github.com/en/actions/security-for-github-actions/security-guides/security-hardening-for-github-actions)).
The inspector shows a redacted value as a marker.

A value `reveal` returns is not a `Secret`, and every surface shows it and every value computed
from it. A sink keeps a secret redacted through the write only when the sink writes it with the
primitive that takes a `Secret` value ([Dependencies](#dependencies)). A sink that calls `reveal`
and writes the plain value leaks it into outbound telemetry.

### Revealing a secret

`reveal(s)` returns the value `s` holds. It is a `@Builtin` of type `Secret(T) => T` and causes no
effect. Every unwrap of a secret is a call of `reveal` in the program's source, as every unwrap in
Rust's `secrecy` crate is a call of `expose_secret`
([secrecy](https://docs.rs/secrecy/latest/secrecy/)). The function a combinator applies reads no
cell and causes nothing, so a `reveal` inside it returns its result only into the `Secret` that
the combinator returns.

A value computed from a secret and meant to leave as a plain value, such as ciphertext or a
signature, leaves through `reveal`: `reveal(key.map(\k -> aes_gcm(k, nonce, pt)))`.

A **verifier** compares a secret in constant time and reveals only the result. `secret_eq` and
`hmac_verify` are library functions over `reveal` and `constant_time_eq` ([The `std::config`
interface](#the-stdconfig-interface)). A webhook checks its signature before it acts on a request,
and a login checks a stored password hash with `secret_eq(stored, argon2id(given, salt))`:

```python
run config::setting(T=Secret(String)) as hook_secret

for r in hooks:
    with begin():
        if config::hmac_verify(hook_secret::get(), r.body, r.sig):
            events << parse(r.body)
```

`hooks` stands for a source whose elements carry a body and a signature. A verifier bounds what one
call reveals, not what many calls reveal: a low-entropy secret, such as a PIN, is recovered through
`secret_eq` by trying every candidate, and limiting attempts is the program's job.

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
| `cambra config set PATH [FILE]` | Sends one value to the setting at `PATH`, with no reload |
| `cambra config list` | Lists each setting by path and type, whether it holds a value, and for a secret an HMAC of the value |

- **A request that leaves a new setting with no value is refused.** The engine compiles the
  version and decodes the payload against each setting's `T`. It refuses the request when a
  setting the version adds has no default and no entry in the payload. A refused request changes
  nothing, as a refused reload does today.
- **The payload's updates commit before the version handles any other input.** A new setting's
  entry is element 0 of its source ([The first value](#the-first-value)). For a setting the reload
  keeps, the entry is an update, and the setting's fold commits it before the version handles
  anything else.
- **A value set without a reload is an update.** `config set` delivers the value to the setting's
  source, and returns once the fold's `value := v` commits in every branch that runs the setting.
  Every transaction that reads after `config set` returns sees the new value.
- **A payload entry reaches every branch.** Settings are shared ([Branches](#branches)), so a value
  in a `cambra branch` or `cambra reload --branch b` request is delivered to every branch that runs
  the setting at that path.
- **The CLI reads values from files, standard input, or its environment.** `--config-env PREFIX`
  sends each environment variable named `PREFIX_<NAME>` as the value of the setting `<NAME>`. A
  value never appears on the command line, which shell history and `/proc/<pid>/cmdline` keep.
  Whatever builds the payload holds the secrets in it.
- **Nothing returns a secret value.** No endpoint reads a secret back. `config list` shows an
  HMAC-SHA256 of each secret under a key the engine holds, as Vault's audit log does ([Audit
  devices](https://developer.hashicorp.com/vault/docs/audit)), so an operator can tell whether a
  value changed or two settings hold the same value. A plain hash would not do: a low-entropy
  secret, such as a PIN or a short password, is recovered from its SHA-256 by trying every
  candidate, and the HMAC's key is what an attacker lacks.

The request's wire shape is **[Open]**: how a value is encoded against its declared type, and how
the payload and a bundle of several modules share one request ([docs/modules.md, "Program
evolution"](modules.md#program-evolution)).

A setting's source is a host-registered source the Configuration API feeds. A reload today installs
a version with no step that feeds a source before the version runs ([program-evolution.md, "How a
reload works"](../src/ccl/design/program-evolution.md#how-a-reload-works)). Committing the payload's
updates first is a requirement on `LiveProgram`'s reload path.

### Held values, renames and removal

A setting's held value is its run's cell. A reload pairs the runs of the two versions by run path
([chl-spec.md, "9.18 Reloading a program of
modules"](chl-spec.md#918-reloading-a-program-of-modules)), so a setting the reload keeps keeps its
value, and a payload that omits it changes nothing.

- **Renames.** `@RenamedFrom` on the run moves the value to the new path. A payload entry for the
  old path is refused as an unknown path.
- **Removal.** A setting holds state, so a reload that drops one is refused unless it marks the run
  with `@Discard`. A cell always holds a value, so a setting goes away by dropping its run, and no
  command unsets it.
- **A change of type.** `T` is an argument of the run, and a run argument that a stored type
  mentions is part of that state's type. The reload carries the held value over when the old `T` is
  a subtype of the new one, and is refused otherwise. A setting whose type changes otherwise is a
  new run at a new path, with the old run marked `@Discard`.

### Remote keystores

A remote keystore is a (sink, source) pair, as `http_serve` is a (source, sink) pair: the program
passes requests to the sink and reads the keystore's replies from the source. The sink's parameter
type takes the credential it sends, such as a Vault token, as a `Secret`. The source decodes each
reply at its declared type and wraps each position the type marks `Secret`, as the Configuration
API does. A reply typed `{token: Secret(String), expires_at: time::Instant}` lets a program
schedule its next refresh from `expires_at` without unwrapping the token. Nothing else about a
keystore is particular to configuration.

Vault is one instance. A credential with a short lease is refreshed on a timer, `time::alarms()`:
each alarm sends a request carrying the token, and each reply is written to a cell that
transactions read. A request per use would put one lease per use on the keystore.

Design work that remains:

- **Outbound pairs.** No source and sink pair for calls made outside the program exists yet.
- **Startup.** A fetched credential is a cell, not a setting, so the request check does not cover
  it. A cell initialized with `first` of the reply source has readers that wait for the first reply,
  as readers of a setting with no value wait.
- **An unreachable keystore.** The cell keeps its last value, and the program decides when a value
  is too old to use.

### Local files [Open]

The engine reads a file on its host, such as a Kubernetes Secret mounted as a volume or a file a
Vault Agent renders, and delivers its contents to a setting, with a new element each time the file
changes. Undecided: whether the program or the engine's deployment names the path, since a path in
the program ties it to one host; how a change is detected; and what a deleted or unreadable file
does to the setting.

## Secret values at rest [Open]

The observation log holds every arrival on a source and every commit's record ([durability.md, "The
observation log"](durability.md#the-observation-log)). What an entry holds is its observation
point's choice. A secret is therefore at rest in three places:

- **The setting's source.** Each value the Configuration API delivers is an arrival, and its entry
  is what the source's observation point records for a `Secret` element.
- **The fold's commit records.** The record of the transaction that commits `value := v` holds `v`.
- **Checkpoints** of any cell whose type holds a `Secret`, including state built from a secret,
  such as a stored outbound request that carries a key. A reload carries that state forward, and a
  branch copies it ([program-evolution.md, "A branch is created by
  branch-and-reload"](../src/ccl/design/program-evolution.md#a-branch-is-created-by-branch-and-reload)).

The candidates for each are: memory only, with every secret supplied again after a restart;
encrypted at rest under a key the engine holds; or one key per value, destroyed to erase the value.

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
never values. A plain setting that a later version replaces with a secret one is a new run, and the
old run's history stays unmarked. [Secret values at rest [Open]](#secret-values-at-rest-open) covers
the rest.

### Code and configuration are applied out of order

Erlang/OTP calls `config_change/3` after the new code is loaded, so new code runs with old
configuration for a moment, and a failed release upgrade restarts on the old release instead of
undoing its steps ([Release handling](https://www.erlang.org/doc/system/release_handling.html)).
Here: a reload commits its payload's updates before the version handles any other input.

### A reader starts before any value arrives

Flink evaluates events that arrive before the broadcast rules against empty state ([Broadcast
state](https://nightlies.apache.org/flink/flink-docs-stable/docs/dev/datastream/fault-tolerance/broadcast_state/)).
Envoy holds initialization until its first configuration arrives, then falls back to a cached value
([xDS protocol](https://www.envoyproxy.io/docs/envoy/latest/api-docs/xds_protocol)). Here: a request
that leaves a new setting with no value and no default is refused. A setting with no value, which
no request checked, has readers that wait, and the rest of the program runs ([The first
value](#the-first-value)).

### Short-lived credentials cannot wait for a reload

Projected Kubernetes ServiceAccount tokens last an hour, and enough clients failed to reread them
that the KEP added a mode extending them to a year
([KEP-1205](https://github.com/kubernetes/enhancements/blob/master/keps/sig-auth/1205-bound-service-account-tokens/README.md)).
Here: `cambra config set` delivers between reloads, and a program refreshes a leased credential
itself ([Remote keystores](#remote-keystores)).

### The configuration type changes across a reload

A setting's held value is state, and a change of `T` is a change of its run's argument ([Held
values, renames and removal](#held-values-renames-and-removal)).

### Valid configuration can still be wrong

Envoy rejects a configuration it cannot apply, keeps the last one it accepted, and reports the
rejected version to the server. Here: a value that fails its type or refinement is refused at the
Configuration API and the setting keeps its last value. A well-typed value that is wrong, an expired
key, is the application's to detect.

## Open questions

- **Rotation.** A transaction reads its key as of its commit, and an outbound request built there
  may leave after a rotation, so the upstream service has to accept the old key until requests
  built with it have drained. AWS's alternating-users rotation keeps the previous credential valid
  for this reason ([Rotation
  strategies](https://docs.aws.amazon.com/secretsmanager/latest/userguide/rotation-strategy.html)).
  The first implementation cuts over: a new value replaces the old at one commit, and a request
  built before it carries the old key.
- **Where secret values live at rest** ([Secret values at rest
  [Open]](#secret-values-at-rest-open)).
- **Local files** ([Local files [Open]](#local-files-open)).
- **Redacting part of a value.** A secret formatted into a string, such as a query string
  `?key=…&q=1`, or into a request body, makes the whole value a `Secret`, and the inspector redacts
  all of it. A format combinator whose result keeps its plain segments visible, or a structured
  body with `Secret` leaves that the sink encodes, would redact only the secret parts.
- **Combining secrets without nesting.** Combining N secrets nests `flat_map` N deep. A second
  `@Builtin` combinator, `using(f)`, would combine any number at one depth. It calls `f` once,
  passing it a function that unwraps any secret, and returns `f`'s result as a `Secret`:
  `using(\unwrap -> unwrap(a) + unwrap(b) + unwrap(c))` is a `Secret`. `using` computes nothing
  that nested `flat_map` does not: inside the innermost function of
  `a.flat_map(\x -> b.flat_map(\y -> …))`, `x` and `y` are plain values, as `unwrap(a)` and
  `unwrap(b)` are. It removes the nesting and nothing else. The unwrapping function exists only as
  `f`'s argument. `f` causes nothing, so it cannot store the function, and the function leaves `f`
  only inside the `Secret` that `using` returns. `using`'s type is
  `((forall (T) Secret(T) => T) => U requires Context except ReadTxn(*)) => Secret(U)`: its argument
  is a function that takes a polymorphic argument, which is **[Open]** and an error ([chl-spec.md,
  "Polymorphic type annotations"](chl-spec.md#polymorphic-type-annotations)). `using` waits on that
  rule.
- **Computing on a secret without a lambda.** Every computation on a secret is a function passed to
  a combinator. A type that names a scope, `In(s, T)` for a value computed under
  `with secrets() as s:`, would let ordinary operators apply to a secret, with the compiler lifting
  each one as `map` does. The cost is inference that is polymorphic over scope labels, and tracking
  of implicit flows: a branch on a labeled value labels every effect inside the branch.
- **Names.** Every name in this document's examples is a placeholder until the design settles:
  `std::config` and its modules and functions, `Secret`, `secret`, `reveal`, the combinators, the
  verifiers, `http::plain` and `http::hidden`, and the CLI's commands.

## Out of scope

These belong to a security design that comes later:

- **Who may reload a program, create a branch, or set a secret.** Whoever can reload a program can
  ship one that sends every secret it holds to a sink, as anyone who can create a Kubernetes Pod can
  read the Secrets it mounts ([Secrets good
  practices](https://kubernetes.io/docs/concepts/security/secrets-good-practices/)). Role-based
  access and policy controls answer it.
- **Code inside the program that is not trusted.** The language does not bound what a function
  reveals. A bound in a function type would claim a defense that the side channels of `flat_map`
  do not deliver: a function a combinator applies can diverge, or take time, depending on the
  secret.
- **Authenticating to the control port.** It has none today. It binds loopback
  (`src/control_port.rs`), so every process on the engine's host reaches it.
- **Idempotent control port requests.** A create or reload request sent twice delivers its
  configuration values twice. An idempotency key on each request is a requirement on the control
  API's design, which has no document yet; the verbs it covers are [program-evolution.md, "The
  control port"](../src/ccl/design/program-evolution.md#the-control-port).
- **How a program authenticates to a remote keystore**, such as short-lived signed tokens bound to
  an audience and a program, as Kubernetes ServiceAccount tokens are.

## Dependencies

- `Secret` as a nominal builtin covariant in `T`, and `secret`, `flat_map` and `reveal` as
  `@Builtin` functions of `std::config` ([chl-spec.md, "9.16 The std
  root"](chl-spec.md#916-the-std-root)).
- `__config_source()`, a `@Builtin` source that the Configuration API feeds, keyed by the path of
  the run that calls it.
- A rule in the spec for `first`, which crosses from a source into a cell: the cell's initial value
  is the source's first element, and a read of the cell waits for it.
- Cells, transactions and per-path footprints as
  [mutability-model.md](../src/ccl/design/mutability-model.md) proposes them, including
  `ReadCell(*)` for the bound on a combinator's function.
- The **[Planned]** inference of an argument left out ([chl-spec.md, "9.4
  Parameters"](chl-spec.md#94-parameters)), for `setting_or`.
- Reloading a program of modules, which pairs runs by run path and carries a run's state
  ([chl-spec.md, "9.18 Reloading a program of
  modules"](chl-spec.md#918-reloading-a-program-of-modules)), since every setting is a run.
- A primitive by which a sink writes a `Secret` value, with outbound telemetry redacting what it
  records of that write. Every sink is built into the engine today, and each one that handles a
  secret writes it through this primitive.
- The std root ([chl-spec.md, "9.16 The std root"](chl-spec.md#916-the-std-root)), which holds
  `std::config`.
- An outbound (sink, source) pair, for remote keystores.
- The observation log's entries for a `Secret` value, for [Secret values at rest
  [Open]](#secret-values-at-rest-open).
