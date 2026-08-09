import Lean.Data.Json
import CclFormal.Ty

/-!
# The wire codec

Hand-written (not derived) so the schema is an explicit, stable contract the
M1 Rust emitter serializes to with plain `serde_json`, rather than whatever
shape a deriving handler happens to produce. Every object carries a `"k"`
discriminant; pairs are 2-arrays.

The parser is `partial` (recursion over `Lean.Json` has no useful structural
measure); it is harness plumbing, not part of the model — nothing is proved
about it, and the smoke `#guard`s below plus the M1 round-trip fuzz are its
gate.
-/

namespace CclFormal

open Lean (Json ToJson FromJson toJson fromJson?)

def BaseTy.toWire : BaseTy → String
  | .int => "Int"
  | .uint => "UInt"
  | .string => "String"
  | .bool => "Bool"
  | .unit => "Unit"

def BaseTy.fromWire : String → Except String BaseTy
  | "Int" => .ok .int
  | "UInt" => .ok .uint
  | "String" => .ok .string
  | "Bool" => .ok .bool
  | "Unit" => .ok .unit
  | s => .error s!"unknown BaseType: {s}"

def FunKind.toWire : FunKind → String
  | .compute => "compute"
  | .data => "data"

def FunKind.fromWire : String → Except String FunKind
  | "compute" => .ok .compute
  | "data" => .ok .data
  | s => .error s!"unknown FunKind: {s}"

instance : ToJson FieldKey where
  toJson
    | .idx n => Json.mkObj [("k", "idx"), ("n", toJson n)]
    | .name s => Json.mkObj [("k", "name"), ("s", toJson s)]

instance : FromJson FieldKey where
  fromJson? j := do
    match (← j.getObjVal? "k").getStr? with
    | .ok "idx" => return .idx (← fromJson? (← j.getObjVal? "n"))
    | .ok "name" => return .name (← fromJson? (← j.getObjVal? "s"))
    | _ => throw s!"unknown FieldKey: {j.compress}"

partial def Pred.toJson : Pred → Json
  | .elem => Json.mkObj [("k", "elem")]
  | .var x => Json.mkObj [("k", "var"), ("x", Lean.toJson x)]
  | .litInt n => Json.mkObj [("k", "litInt"), ("n", Lean.toJson n)]
  | .litBool b => Json.mkObj [("k", "litBool"), ("b", Lean.toJson b)]
  | .litStr s => Json.mkObj [("k", "litStr"), ("s", Lean.toJson s)]
  | .litUnit => Json.mkObj [("k", "litUnit")]
  | .unop op a => Json.mkObj [("k", "unop"), ("op", Lean.toJson op), ("a", a.toJson)]
  | .binop op a b =>
      Json.mkObj [("k", "binop"), ("op", Lean.toJson op), ("a", a.toJson), ("b", b.toJson)]
  | .proj a key => Json.mkObj [("k", "proj"), ("a", a.toJson), ("key", Lean.toJson key)]
  | .app f a => Json.mkObj [("k", "app"), ("f", f.toJson), ("a", a.toJson)]

partial def Pred.fromJson? (j : Json) : Except String Pred := do
  match (← j.getObjVal? "k").getStr? with
  | .ok "elem" => return .elem
  | .ok "var" => return .var (← Lean.fromJson? (← j.getObjVal? "x"))
  | .ok "litInt" => return .litInt (← Lean.fromJson? (← j.getObjVal? "n"))
  | .ok "litBool" => return .litBool (← Lean.fromJson? (← j.getObjVal? "b"))
  | .ok "litStr" => return .litStr (← Lean.fromJson? (← j.getObjVal? "s"))
  | .ok "litUnit" => return .litUnit
  | .ok "unop" =>
      return .unop (← Lean.fromJson? (← j.getObjVal? "op"))
        (← Pred.fromJson? (← j.getObjVal? "a"))
  | .ok "binop" =>
      return .binop (← Lean.fromJson? (← j.getObjVal? "op"))
        (← Pred.fromJson? (← j.getObjVal? "a"))
        (← Pred.fromJson? (← j.getObjVal? "b"))
  | .ok "proj" =>
      return .proj (← Pred.fromJson? (← j.getObjVal? "a"))
        (← Lean.fromJson? (← j.getObjVal? "key"))
  | .ok "app" =>
      return .app (← Pred.fromJson? (← j.getObjVal? "f"))
        (← Pred.fromJson? (← j.getObjVal? "a"))
  | _ => throw s!"unknown Pred: {j.compress}"

instance : ToJson Pred := ⟨Pred.toJson⟩
instance : FromJson Pred := ⟨Pred.fromJson?⟩

partial def Ty.toJson : Ty → Json
  | .base b => Json.mkObj [("k", "base"), ("base", Lean.toJson b.toWire)]
  | .uintRange n => Json.mkObj [("k", "uintRange"), ("n", Lean.toJson n)]
  | .dataSource s => Json.mkObj [("k", "dataSource"), ("name", Lean.toJson s)]
  | .txn => Json.mkObj [("k", "txn")]
  | .fn n k d c =>
      Json.mkObj [("k", "fn"),
        ("binder", match n with | some s => Lean.toJson s | none => Json.null),
        ("kind", Lean.toJson k.toWire), ("dom", d.toJson), ("cod", c.toJson)]
  | .tuple ts => Json.mkObj [("k", "tuple"), ("ts", Json.arr (ts.map Ty.toJson).toArray)]
  | .record fs =>
      Json.mkObj [("k", "record"),
        ("fields", Json.arr (fs.map fun (n, t) =>
          Json.arr #[Lean.toJson n, t.toJson]).toArray)]
  | .variant tags =>
      Json.mkObj [("k", "variant"),
        ("tags", Json.arr (tags.map fun (key, t) =>
          Json.arr #[Lean.toJson key, t.toJson]).toArray)]
  | .refined b p => Json.mkObj [("k", "refined"), ("base", b.toJson), ("pred", Lean.toJson p)]

mutual

partial def Ty.fromJson? (j : Json) : Except String Ty := do
  match (← j.getObjVal? "k").getStr? with
  | .ok "base" => return .base (← BaseTy.fromWire (← (← j.getObjVal? "base").getStr?))
  | .ok "uintRange" => return .uintRange (← Lean.fromJson? (← j.getObjVal? "n"))
  | .ok "dataSource" => return .dataSource (← Lean.fromJson? (← j.getObjVal? "name"))
  | .ok "txn" => return .txn
  | .ok "fn" =>
      let binder ← match ← j.getObjVal? "binder" with
        | Json.null => pure none
        | b => some <$> Lean.fromJson? b
      return .fn binder (← FunKind.fromWire (← (← j.getObjVal? "kind").getStr?))
        (← Ty.fromJson? (← j.getObjVal? "dom")) (← Ty.fromJson? (← j.getObjVal? "cod"))
  | .ok "tuple" =>
      let ts ← (← (← j.getObjVal? "ts").getArr?).toList.mapM Ty.fromJson?
      return .tuple ts
  | .ok "record" =>
      let fs ← (← (← j.getObjVal? "fields").getArr?).toList.mapM
        (pairFromJson? Lean.fromJson?)
      return .record fs
  | .ok "variant" =>
      let tags ← (← (← j.getObjVal? "tags").getArr?).toList.mapM
        (pairFromJson? Lean.fromJson?)
      return .variant tags
  | .ok "refined" =>
      return .refined (← Ty.fromJson? (← j.getObjVal? "base"))
        (← Lean.fromJson? (← j.getObjVal? "pred"))
  | _ => throw s!"unknown Ty: {j.compress}"

/-- A `[key, ty]` 2-array pair (record field / variant tag). -/
partial def pairFromJson? (f : Json → Except String α) (e : Json) :
    Except String (α × Ty) := do
  match ← e.getArr? with
  | #[k, t] => return (← f k, ← Ty.fromJson? t)
  | _ => throw s!"expected a 2-array pair: {e.compress}"

end

instance : ToJson Ty := ⟨Ty.toJson⟩
instance : FromJson Ty := ⟨Ty.fromJson?⟩

/-- Round-trip smoke checks (`BEq`-compared; `beq ↔ eq` is a later step). -/
private def roundTrips (t : Ty) : Bool :=
  match (Lean.fromJson? (Lean.toJson t) : Except String Ty) with
  | .ok t' => t == t'
  | .error _ => false

#guard roundTrips (.base .int)
#guard roundTrips (.fn (some "x") .data (.uintRange 3)
  (.refined (.base .int) (.binop "eq" .elem (.var "x"))))
#guard roundTrips (.record [("a", .base .bool), ("b", .tuple [.txn, .dataSource "s"])])
#guard roundTrips (.variant [(.idx 0, .base .unit), (.name "tag", .base .string)])

end CclFormal
