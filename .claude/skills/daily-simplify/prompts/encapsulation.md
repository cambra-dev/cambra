# Category brief: encapsulation & coupling

Append this to the finder prompt for the `encapsulation` category.

---

## What you are hunting

Find a fact that one module owns and that another module **re-derives or re-asserts** instead of
receiving it. Each such site is coupling: the consumer depends on how the owner works, and it
changes when the owner changes. The fix gives the fact one owner. The owner establishes the fact
once at its boundary and hands consumers something that already carries it: a restricted type, a
smart constructor, a value it computed, or a narrower interface.

Input sanitization is the classic example. Sanitize at the boundary and wrap the result in a
restricted type, so no consumer repeats the check.

### What is not a candidate

Cheap verification at an input is fine, and so is a check that serves as a proxy signal. Leave
these alone:

- `debug_assert!`, `unreachable!` and invariant checks at pass boundaries. `CLAUDE.md` asks for
  them.
- Type checking re-run after inference to confirm that later transformations did not break
  anything. This redundancy is deliberate: it is a tripwire that guards the transformations.
- Any check whose only consequence is to fail loudly.

The test: **does the consumer's behaviour depend on the re-derivation?** If the consumer only
asserts and panics, it is verification and stays. If the consumer branches on what it derived,
recomputes something to use the result, or carries real logic for a case the owner already rules
out, the derivation is load-bearing. Then it is a candidate.

### Symptoms

- **Re-derived results.** A pass recomputes an analysis that an earlier pass already computed and
  could carry, such as free variables, types, scopes or a shape classification.
- **Logic for impossible cases.** A consumer has a fallback or recovery path for input the
  producer never emits. The convoluted part is that real code exists for a case that cannot
  happen.
- **Reaching into a representation.** A module matches on another module's enum internals, touches
  its fields, or depends on its internal ordering, where the owner could expose the answer
  directly.
- **Visibility that lets outsiders bypass a constructor.** `pub` fields or items let other modules
  build a value that breaks an invariant, so every consumer has to defend against that value. The
  seeds' `redundant_pub_crate` list is a starting point.
- **Conventions with no owner.** Generated-name prefixes, magic strings, or "phase X has already
  removed Y" assumptions, decoded in several modules with no single definition.
- **Implicit concepts.** A concept the code uses without naming it, or a special case that reveals
  a missing distinction. The signal must come from existing code or semantics.

### Seeds

- "Files that change together": pairs of files that often appear in the same commit. A pair whose
  co-changes are not explained by a direct call or type dependency suggests shared knowledge with no
  owner.
- "Defensive-handling markers": comments that admit to handling a case the code believes cannot
  happen.
- The `use crate::` edge table: a back-edge against the pipeline direction in `src/design.md`.

### Extra fields for every candidate

- **owner:** the module that should own the fact, and where it establishes the fact today, if it
  does.
- **producers:** every path that produces input for the boundary. Include test helpers, the
  inspector, hot reload and any other constructor. This is the list that makes the candidate safe.
  If even one producer does not establish the fact, the downstream logic is load-bearing. In that
  case, either name the change to that producer or drop the candidate.
- **re-derivations:** every site that would be deleted, each marked load-bearing or verification.
  Only the load-bearing sites go.

A change that moves ownership across a pass boundary is a structural finding, not a candidate. A
separate IR type per phase is one example.
