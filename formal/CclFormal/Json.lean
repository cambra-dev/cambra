import Lean.Data.Json
import CclFormal.Ty
import CclFormal.Merge

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
  | .piBound k => Json.mkObj [("k", "piBound"), ("i", Lean.toJson k)]
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
  | .ok "piBound" => return .piBound (← Lean.fromJson? (← j.getObjVal? "i"))
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
  | .refined b ps =>
      Json.mkObj [("k", "refined"), ("base", b.toJson),
        ("refinements", Json.arr (ps.map Lean.toJson).toArray)]

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
        (← Lean.fromJson? (← j.getObjVal? "refinements"))
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

/-! ## The compact type

`CTy` is the merge model's mirror of `CompactType` (`CclFormal/Merge.lean`), and
this codec is the contract `differential.rs` serializes a real `CompactType` to.
The two abstractions the model makes are applied *by the encoder*, so the wire
carries only what the model can express: the domain slot is `some d` for a single
alternative and `null` for two or more, and a conflicted slot's domain payload is
`null` because coalesce reads it only for a diagnostic. Variable identities and
history slots have no field — the model drops both. -/

def KindM.toWire : KindM → String
  | .data => "data"
  | .compute => "compute"
  | .conflict => "conflict"
  | .unknown => "unknown"

def KindM.fromWire : String → Except String KindM
  | "data" => .ok .data
  | "compute" => .ok .compute
  | "conflict" => .ok .conflict
  | "unknown" => .ok .unknown
  | s => .error s!"unknown KindMerge: {s}"

def Atom.toJson : Atom → Json
  | .prim b => Json.mkObj [("k", "prim"), ("base", Lean.toJson b.toWire)]
  | .uintRange n => Json.mkObj [("k", "uintRange"), ("n", Lean.toJson n)]
  | .source s => Json.mkObj [("k", "source"), ("s", Lean.toJson s)]
  | .txn => Json.mkObj [("k", "txn")]

def Atom.fromJson? (j : Json) : Except String Atom := do
  match (← j.getObjVal? "k").getStr? with
  | .ok "prim" => return .prim (← BaseTy.fromWire (← (← j.getObjVal? "base").getStr?))
  | .ok "uintRange" => return .uintRange (← Lean.fromJson? (← j.getObjVal? "n"))
  | .ok "source" => return .source (← Lean.fromJson? (← j.getObjVal? "s"))
  | .ok "txn" => return .txn
  | _ => throw s!"unknown Atom: {j.compress}"

instance : ToJson Atom := ⟨Atom.toJson⟩
instance : FromJson Atom := ⟨Atom.fromJson?⟩

namespace CTy

partial def toJson : CTy → Json
  | .mk atoms recF varT fn refinements =>
      let mapJson : List (FieldKey × CTy) → Json := fun m =>
        Json.arr (m.map fun (k, w) => Json.arr #[Lean.toJson k, toJson w]).toArray
      Json.mkObj
        [("atoms", Json.arr (atoms.map Atom.toJson).toArray),
         ("rec", match recF with | none => Json.null | some m => mapJson m),
         ("var", match varT with | none => Json.null | some m => mapJson m),
         ("fn", match fn with
                | none => Json.null
                | some (k, ds, cod) =>
                    Json.mkObj [("kind", Lean.toJson k.toWire),
                      ("doms", Json.arr (ds.map toJson).toArray),
                      ("cod", toJson cod)]),
         ("refinements", match refinements with
                    | none => Json.null
                    | some ps => Json.arr (ps.map Lean.toJson).toArray)]

mutual

partial def fromJson? (j : Json) : Except String CTy := do
  let atoms ← (← (← j.getObjVal? "atoms").getArr?).toList.mapM Atom.fromJson?
  let recF ← optMap (← j.getObjVal? "rec")
  let varT ← optMap (← j.getObjVal? "var")
  let fn ← match ← j.getObjVal? "fn" with
    | Json.null => pure none
    | f => do
      let k ← KindM.fromWire (← (← f.getObjVal? "kind").getStr?)
      let ds ← (← (← f.getObjVal? "doms").getArr?).toList.mapM fromJson?
      let cod ← fromJson? (← f.getObjVal? "cod")
      pure (some (k, ds, cod))
  let refinements ← match ← j.getObjVal? "refinements" with
    | Json.null => pure none
    | c => some <$> Lean.fromJson? c
  return .mk atoms recF varT fn refinements

/-- A `null`-or-array keyed map: the `Option (List (FieldKey × CTy))` slots. -/
partial def optMap (j : Json) : Except String (Option (List (FieldKey × CTy))) := do
  match j with
  | Json.null => return none
  | _ =>
    let entries ← (← j.getArr?).toList.mapM fun e => do
      match ← e.getArr? with
      | #[k, w] => do
        let key : FieldKey ← Lean.fromJson? k
        let payload ← fromJson? w
        pure (key, payload)
      | _ => throw s!"expected a 2-array pair: {e.compress}"
    return some entries

end

end CTy

instance : ToJson CTy := ⟨CTy.toJson⟩
instance : FromJson CTy := ⟨CTy.fromJson?⟩

/-- Round-trip smoke checks (`BEq`-compared; `beq ↔ eq` is a later step). -/
private def roundTrips (t : Ty) : Bool :=
  match (Lean.fromJson? (Lean.toJson t) : Except String Ty) with
  | .ok t' => t == t'
  | .error _ => false

#guard roundTrips (.base .int)
#guard roundTrips (.fn (some "x") .data (.uintRange 3)
  (.refined (.base .int) [.binop "eq" .elem (.var "x")]))
-- A multi-refinement position round-trips too: the wire carries the whole set.
#guard roundTrips (.refined (.base .int)
  [.binop "eq" .elem (.var "x"), .binop "eq" .elem (.var "y")])
#guard roundTrips (.record [("a", .base .bool), ("b", .tuple [.txn, .dataSource "s"])])
#guard roundTrips (.variant [(.idx 0, .base .unit), (.name "tag", .base .string)])

/-- The same smoke check for the compact type. -/
private def cRoundTrips (t : CTy) : Bool :=
  match (CTy.fromJson? (CTy.toJson t) : Except String CTy) with
  | .ok t' => CTy.eqv t t'
  | .error _ => false

-- `none` refinements (no contribution) and `some []` (a value guaranteeing nothing)
-- are distinct on the wire, which is the whole point of the slot's sentinel.
#guard cRoundTrips (.mk [] none none none none)
#guard cRoundTrips (.mk [] none none none (some []))
#guard !CTy.eqv (.mk [] none none none none) (.mk [] none none none (some []))
#guard cRoundTrips (.mk [.prim .int, .txn, .uintRange 3, .source "s"] none none none
  (some [.binop "eq" .elem (.litInt 1)]))
-- Every slot at once, including a `null` ("two or more") domain and a conflicted kind.
#guard cRoundTrips (.mk [.prim .bool]
  (some [(.idx 0, .mk [.prim .int] none none none (some []))])
  (some [(.name "tag", .mk [] none none none none)])
  (some (.conflict, [], .mk [.prim .string] none none none (some []))) (some []))
#guard cRoundTrips (.mk [] none none
  (some (.unknown, [.mk [.prim .int] none none none (some []),
      .mk [.prim .bool] none none none (some [])],
    .mk [] (some []) none none none)) (some []))

end CclFormal
