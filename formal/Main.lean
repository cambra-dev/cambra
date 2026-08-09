import CclFormal

/-!
# The M1 ground-subtype oracle

Reads JSONL from stdin — one `{"lhs": <Ty>, "rhs": <Ty>}` object per line —
and answers one verdict line per case: `true` / `false` (the model's
`subCheck` under identity morphisms), or `error: …` when a line does not
decode as a ground pair. An empty line (or EOF) terminates.

The Rust half lives in `src/ccl/infer/solver/differential.rs`, which
generates biased ground pairs, computes `constrain_subtype`'s verdict, and
diffs against this oracle.
-/

open CclFormal

def verdict (line : String) : String :=
  match Lean.Json.parse line with
  | .error e => s!"error: parse: {e}"
  | .ok j =>
      let checked : Except String Bool := do
        let lhs ← Ty.fromJson? (← j.getObjVal? "lhs")
        let rhs ← Ty.fromJson? (← j.getObjVal? "rhs")
        pure (subCheck Ren.id Ren.id lhs rhs)
      match checked with
      | .error e => s!"error: decode: {e}"
      | .ok b => toString b

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
