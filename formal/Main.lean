import CclFormal

/-!
# The differential oracle

Reads JSONL from stdin — one case object per line, tagged by `"op"` — and answers one verdict line
per case, or `error: …` when a line does not decode. An empty line (or EOF) terminates.

- `"sub"`: `true` / `false`, the model's `subtypeCheck` on a concrete type pair.
- `"merge"`: `ok`, or `mismatch: <CompactTy>` carrying the model's own merged bound.
- `"mergeKind"`: the same, for a Σ binder's kind.
- `"refuses"`: `ok`, or `mismatch: <Bool>` carrying the model's own verdict.
- `"coalesce"`: `ok`, or `mismatch: <outcome>` carrying the model's own.

The Rust half lives in `tests/differential_oracle.rs`, which generates the cases, computes the
solver's answer, and diffs it against this oracle.
-/

open CclFormal

/-- `{"op":"sub","lhs":<Ty>,"rhs":<Ty>}` — the concrete subtype verdict. -/
def subVerdict (j : Lean.Json) : Except String String := do
  let lhs ← Ty.fromJson? (← j.getObjVal? "lhs")
  let rhs ← Ty.fromJson? (← j.getObjVal? "rhs")
  pure (toString (subtypeCheck lhs rhs))

/-- `{"op":"merge","pol":<Bool>,"lhs":<CompactTy>,"rhs":<CompactTy>,"got":<CompactTy>}` —
whether the
Rust's merged bound is the model's, judged by `equiv`, the equality every theorem in
`CclFormal/Merge.lean` is stated up to. A mismatch answers with the model's own
result so the diff is in the failure message rather than in a second run. -/
def mergeVerdict (j : Lean.Json) : Except String String := do
  let pol ← Lean.fromJson? (← j.getObjVal? "pol")
  let lhs ← CompactTy.fromJson? (← j.getObjVal? "lhs")
  let rhs ← CompactTy.fromJson? (← j.getObjVal? "rhs")
  let got ← CompactTy.fromJson? (← j.getObjVal? "got")
  let want := CompactTy.merge pol lhs rhs
  pure (if CompactTy.equiv want got then "ok" else s!"mismatch: {(CompactTy.toJson want).compress}")

/-- `{"op":"mergeKind","pol":<Bool>,"lhs":<CompactTypeKind>,"rhs":<CompactTypeKind>,
"got":<CompactTypeKind>}` — whether the Rust's merged kind is the model's, judged by
`equivTypeKind`, the equality every law in `CclFormal/TypeKindMerge.lean` is stated up to.

This is the operation nothing else compares. The polar merge oracle cannot reach it: the
model's `CompactTy` has no Σ binder slot, so `cty_json` refuses a bound carrying binders and
every case that would exercise a kind is filtered out before the wire. -/
def mergeKindVerdict (j : Lean.Json) : Except String String := do
  let pol ← Lean.fromJson? (← j.getObjVal? "pol")
  let lhs ← CompactTypeKind.fromJson? (← j.getObjVal? "lhs")
  let rhs ← CompactTypeKind.fromJson? (← j.getObjVal? "rhs")
  let got ← CompactTypeKind.fromJson? (← j.getObjVal? "got")
  let want := CompactTypeKind.mergeTypeKind pol lhs rhs
  pure (if CompactTypeKind.equivTypeKind want got then "ok"
        else s!"mismatch: {(CompactTypeKind.toJson want).compress}")

/-- `{"op":"refuses","kind":<TypeKind>,"ty":<Ty>,"got":<Bool>}` — whether the solver's certain
non-membership verdict is the model's.

The half of membership a caller may act on, and the one every caller of it turns into a
rejection, so a disagreement here is a program refused or an error missed.
`not_admits_of_refuses` proves a refusal never lands on a member; this checks that the two
sides refuse the same things. -/
def refusesVerdict (j : Lean.Json) : Except String String := do
  let kind ← TypeKind.fromJson? (← j.getObjVal? "kind")
  let ty ← Ty.fromJson? (← j.getObjVal? "ty")
  let got : Bool ← Lean.fromJson? (← j.getObjVal? "got")
  let want := refuses kind ty
  pure (if want == got then "ok" else s!"mismatch: {want}")

/-- `{"op":"coalesce","pol":<Bool>,"ct":<CompactTy>,"got":<outcome>}` — whether the
solver's materialization of a bound is the model's. The outcome is `{"k":"ok","ty":<Ty>}`,
`{"k":"unresolved"}` for a position that materialized to a fresh inference variable, or
`{"k":"err","kind":<CoalesceError>}`. A mismatch
answers with the model's own outcome. -/
def coalesceVerdict (j : Lean.Json) : Except String String := do
  let pol ← Lean.fromJson? (← j.getObjVal? "pol")
  let ct ← CompactTy.fromJson? (← j.getObjVal? "ct")
  let g ← j.getObjVal? "got"
  let got : CompactTy.CoalesceOutcome ← match ← (← g.getObjVal? "k").getStr? with
    | "ok" => .ok <$> Ty.fromJson? (← g.getObjVal? "ty")
    | "unresolved" => pure .unresolved
    | "err" => .err <$> (← g.getObjVal? "kind").getStr?
    | k => throw s!"unknown coalesce outcome: {k}"
  let want := CompactTy.coalesce pol ct
  if CompactTy.coalesceAgrees want got then
    pure "ok"
  else
    pure <| "mismatch: " ++
      (match want with
       | .ok none => "unresolved"
       | .ok (some t) => (Ty.toJson t).compress
       | .error e => s!"error {repr e}")

def verdict (line : String) : String :=
  match Lean.Json.parse line with
  | .error e => s!"error: parse: {e}"
  | .ok j =>
      let checked : Except String String := do
        match ← (← j.getObjVal? "op").getStr? with
        | "sub" => subVerdict j
        | "merge" => mergeVerdict j
        | "mergeKind" => mergeKindVerdict j
        | "refuses" => refusesVerdict j
        | "coalesce" => coalesceVerdict j
        | op => throw s!"unknown op: {op}"
      match checked with
      | .error e => s!"error: decode: {e}"
      | .ok answer => answer

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    let raw ← stdin.getLine
    let line := raw.trimAscii.toString
    if line.isEmpty then
      break
    stdout.putStrLn (verdict line)
    stdout.flush
