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
  which only a `SecretReader` scope extracts ([Secret configuration](#secret-configuration)).
- **`SecretReader` scope**: a scope the program writes that supplies `SecretReader` to its body.
- **Configuration payload**: the map from configuration-source name to an encoded value that a
  create or reload request carries beside the program.
- **Configuration API**: the engine endpoint that decodes a configuration payload and delivers each
  entry to the configuration source of that name. Some of what it delivers is secret.

## Configuration is a source

A configuration source is an ordinary source at the CHL layer: opening one requires `Ext`, its
elements are values, and every rule of [chl-spec.md, "7.3 Sources"](chl-spec.md#73-sources) holds.
`std::config` declares it, in the std root ([chl-spec.md, "9.16 The std
root"](chl-spec.md#916-the-std-root)). The spelling below is a sketch:

```python
import std::config

type Payments = {base_url: String, timeout_ms: Int}
type PaymentsKey = {api_key: String}

payments: Source(Payments) = config::source("payments")
payments_key: Source(Secret(PaymentsKey)) = config::secret("payments_key")
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
| `secret(name)` | `String => Source(Secret(T))` | Declares the secret configuration source `name` |
| `source_or(name, default)` | `{String, T} => Source(T)` | Declares `name` with `default` as its value until one is supplied |
| `first(s)` | `Source(T) => T` | The value `s` holds when the version starts, which a mutable variable's declaration takes as its initial value |
| `Secret(T)` | nominal type | `Secret::new(v)` constructs one; `s.extract()` and the pattern `Secret::new(v)` read one, and require `SecretReader` |
| `secrets()` | scope marker | `with secrets():` supplies `SecretReader` to its body |

Opening a source requires `Ext`, so `source`, `secret`, `source_or` and `first` are called at a
module's top level. `T` is a type parameter inferred from the annotation or from `default`.

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
`config::secret("payments_key_staging")`, and the Configuration API delivers to it by that name.

## Secret configuration

A secret configuration source's elements have type **`Secret(T)`**, a nominal type of the
single-constructor form ([chl-spec.md, "6.8 Nominal types and methods
[Decided]"](chl-spec.md#68-nominal-types-and-methods-decided)): `Secret::new(v)` constructs one and
`s.extract()` reads it. A `Secret(T)` is a value like any other until it is extracted: a program
stores it, passes it, and folds it into a mutable variable. Extracting it, by `extract` or by the
pattern `Secret::new(v)`, requires **`SecretReader`**, as reading a transactional mutable variable
requires `Transaction` ([chl-spec.md, "8.3 Reads"](chl-spec.md#83-reads)). A scope the program
writes supplies `SecretReader` to its body, as `with begin():` supplies `Transaction`, and nothing
else supplies it, the run included. Inside the scope an extracted value is printed and composed as
any value is. The spelling below is a placeholder:

```python
key: Mut(Secret(PaymentsKey), Txn) := config::first(payments_key)
for k in payments_key:
    with begin():
        key := k                               # storing a Secret extracts nothing

for req in charges:
    with begin():
        with secrets():                        # supplies SecretReader to its body
            auth = "Bearer " + key.extract().api_key
            payments_api << (auth: auth, body: req)
```

Reading `key` requires `Transaction`, because the fold stores it in a transactional mutable
variable, and extracting it requires `SecretReader`. A loop over the source itself extracts each
element with `SecretReader` alone. `payments_api` is a sink for outbound requests, which is not
designed yet. A sink or source that receives an extracted value manages it, its error text included.

### Extracting confines the value to its scope

**No value computed from an extracted secret leaves the scope that extracted it,** except into a
sink. A write to a mutable variable or a feed bound outside the scope, a function value that
outlives it, and the scope's own value are each a compile error at the line that writes it. A value
leaves a scope as a secret when the scope constructs one, `Secret::new(v)`, which requires nothing.
The effects stack has a rule of the same form: nothing that outlives a scope names a variable whose
history the scope ends.

The rule exists for this program, which `SecretReader` alone accepts:

```python
leaked: Feed(String)
for req in charges:
    with begin():
        with secrets():
            leaked << key.extract().api_key   # extracting requires SecretReader
for s in leaked:
    log << s                                  # s is a String; nothing here requires SecretReader
```

A requirement gates the operation that needs it, not the value that operation returns. Under
[chl-spec.md, "6.9 Effects in function types
[Tentative]"](chl-spec.md#69-effects-in-function-types-tentative), as the effects stack under review
revises it, "opening a source requires `Ext`. The source's elements are values, so a function that
reads a captured source requires nothing further":

```python
reqs, resps = http_serve("8080", "POST", "/echo")    # opening the source requires Ext

def shout(s): s + "!"                                 # requires nothing
for r in reqs:
    resps << shout(r)                                 # r is a String; nothing here requires Ext
```

A transactional read has the same shape. The read requires `Transaction`, and the value it returns
leaves the block through a feed:

```python
balance: Mut(Int, Txn) := 0
audit: Feed(Int)
for r in reqs:
    with begin():
        audit << balance           # the read requires Transaction
for b in audit:
    log << b                       # b is an Int; nothing here requires Transaction
```

The confinement makes the requirement sufficient for redaction. Every term that sees an extracted
value requires `SecretReader`, and inference records each term's requirements, so the inspector, the
control port's replies, errors and the engine's logs redact every term that requires `SecretReader`
and every `Secret`-typed value. Redaction is decided from types, never by matching a value's text,
which GitHub Actions does and which misses an encoded or reformatted copy ([Security
hardening](https://docs.github.com/en/actions/security-for-github-actions/security-guides/security-hardening-for-github-actions)).
The inspector shows a redacted value as a marker.

### Confinement follows data

A value a condition on a secret selects leaves the scope. Confinement covers what an extracted value
flows into, not what it decides, and keeping a selection private is the program's choice of where
its scopes end:

```python
allowed: Mut(Secret(Set(Int)), Txn) := config::first(admin_ids)   # folded as above

with begin():
    with secrets():
        admins = [u for u in users if u.id in allowed.extract()]
notify << admins                   # leaves the scope: its elements are users, not the secret
```

Every element of `admins` is a user, and none is secret. Which users it holds is the intersection of
`users` and the secret set, so `admins`, its size and the time it arrives show that much of the
secret, in the inspector as anywhere else. A conditional expression is the same case: `"yes" if
guess == pin.extract() else "no"` leaves the scope and tells whoever reads it whether the guess was
right. A program that must keep a selection private uses it inside the scope, or leaves with
`Secret::new(admins)`. Confining selections too would mean tracking every value a secret condition
decides, downstream of every branch and filter.

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
feeds requests to the sink and reads the keystore's replies from the source. A request that carries
a secret, such as a Vault token, is fed inside a `SecretReader` scope, and a reply that holds one
arrives as a `Secret`. Nothing else about a keystore is particular to configuration.

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
- **Names.** Every name in this document's examples is a placeholder until the design settles:
  `std::config` and its functions, `Secret`, `SecretReader`, the scope that supplies it, and the
  CLI's commands. `Secret::new` and `extract` are the names every single-constructor nominal type
  has.

## Out of scope

These belong to a security design that comes later:

- **Who may reload a program, create a branch, set a secret, or add a scope that extracts one.**
  Whoever can reload a program can ship one that sends every secret it extracts to a sink, as anyone
  who can create a Kubernetes Pod can read the Secrets it mounts ([Secrets good
  practices](https://kubernetes.io/docs/concepts/security/secrets-good-practices/)). Role-based
  access and policy controls, such as a policy naming the sinks a secret may reach, answer it.
- **Authenticating to the control port.** It has none today and binds every interface
  (`src/control_port.rs`).
- **Idempotent control port requests.** A create or reload request sent twice appends its
  configuration values twice. An idempotency key on each request is a requirement on the control
  API's design, which has no document yet; the verbs it covers are [program-evolution.md, "The
  control port"](../src/ccl/design/program-evolution.md#the-control-port).
- **How a program authenticates to a remote keystore**, such as short-lived signed tokens bound to
  an audience and a program, as Kubernetes ServiceAccount tokens are.

## Dependencies

- The effects design, for `SecretReader` and the `Ext` that opening a source requires.
- A way for `std::config` to state that `Secret`'s `extract` and its pattern require `SecretReader`.
  The single-constructor form declares `extract` with no `requires` clause.
- The std root ([chl-spec.md, "9.16 The std root"](chl-spec.md#916-the-std-root)), which holds
  `std::config`.
- An outbound (sink, source) pair, for remote keystores.
- A reload of a program of several modules ([docs/modules.md, "Program
  evolution"](modules.md#program-evolution)), since `std::config` is a module.
- Durable state, for [Secret values at rest [Open]](#secret-values-at-rest-open).
