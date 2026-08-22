import CclFormal

/-!
# The differential oracle

Reads JSONL from stdin — one case object per line, tagged by `"op"` — and answers
one verdict line per case, or `error: …` when a line does not decode. An empty
line (or EOF) terminates.

- `"sub"`: `true` / `false`, the model's `subCheck` on a ground type pair.
- `"merge"`: `ok`, or `mismatch: <CTy>` carrying the model's own merged bound.
- `"coalesce"`: `ok`, or `mismatch: <outcome>` carrying the model's own.

The Rust half lives in `tests/differential_oracle.rs`, which generates
the cases, computes the solver's answer, and diffs it against this oracle.
-/

open CclFormal

/-- `{"op":"sub","lhs":<Ty>,"rhs":<Ty>}` — the ground subtype verdict. -/
def subVerdict (j : Lean.Json) : Except String String := do
  let lhs ← Ty.fromJson? (← j.getObjVal? "lhs")
  let rhs ← Ty.fromJson? (← j.getObjVal? "rhs")
  pure (toString (subCheck lhs rhs))

/-- `{"op":"merge","pol":<Bool>,"lhs":<CTy>,"rhs":<CTy>,"got":<CTy>}` — whether the
Rust's merged bound is the model's, judged by `eqv`, the equality every theorem in
`CclFormal/Merge.lean` is stated up to. A mismatch answers with the model's own
result so the diff is in the failure message rather than in a second run. -/
def mergeVerdict (j : Lean.Json) : Except String String := do
  let pol ← Lean.fromJson? (← j.getObjVal? "pol")
  let lhs ← CTy.fromJson? (← j.getObjVal? "lhs")
  let rhs ← CTy.fromJson? (← j.getObjVal? "rhs")
  let got ← CTy.fromJson? (← j.getObjVal? "got")
  let want := CTy.merge pol lhs rhs
  pure (if CTy.eqv want got then "ok" else s!"mismatch: {(CTy.toJson want).compress}")

/-- `{"op":"coalesce","pol":<Bool>,"ct":<CTy>,"got":<outcome>}` — whether the
solver's materialization of a bound is the model's. The outcome is
`{"k":"ok","ty":<Ty>}`, `{"k":"unresolved"}` for a position that materialized to a
fresh inference variable, or `{"k":"err","kind":<CoalesceError>}`. A mismatch
answers with the model's own outcome. -/
def coalesceVerdict (j : Lean.Json) : Except String String := do
  let pol ← Lean.fromJson? (← j.getObjVal? "pol")
  let ct ← CTy.fromJson? (← j.getObjVal? "ct")
  let g ← j.getObjVal? "got"
  let got : CTy.CoGot ← match ← (← g.getObjVal? "k").getStr? with
    | "ok" => .ok <$> Ty.fromJson? (← g.getObjVal? "ty")
    | "unresolved" => pure .unresolved
    | "err" => .err <$> (← g.getObjVal? "kind").getStr?
    | k => throw s!"unknown coalesce outcome: {k}"
  let want := CTy.coalesce pol ct
  if CTy.coalesceAgrees want got then
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
