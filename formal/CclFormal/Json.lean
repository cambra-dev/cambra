import Lean.Data.Json
import CclFormal.Ty
import CclFormal.Merge

/-!
# The wire codec

Hand-written (not derived) so the schema is an explicit, stable contract the Rust emitter serializes
to with plain `serde_json`, rather than whatever shape a deriving handler happens to produce. Every
object carries a `"k"` discriminant; pairs are 2-arrays.

The parser is `partial` (recursion over `Lean.Json` has no useful structural measure); it is harness
plumbing, not part of the model — nothing is proved about it, and the smoke `#guard`s below plus the
differential oracles are its gate.
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

partial def Predicate.toJson : Predicate → Json
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
  | .lam body => Json.mkObj [("k", "lam"), ("body", body.toJson)]
  | .boundVar k => Json.mkObj [("k", "boundVar"), ("i", Lean.toJson k)]
  | .cast v refs =>
      Json.mkObj
        [("k", "cast"), ("v", v.toJson), ("refs", Json.arr (refs.map Predicate.toJson).toArray)]

partial def Predicate.fromJson? (j : Json) : Except String Predicate := do
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
        (← Predicate.fromJson? (← j.getObjVal? "a"))
  | .ok "binop" =>
      return .binop (← Lean.fromJson? (← j.getObjVal? "op"))
        (← Predicate.fromJson? (← j.getObjVal? "a"))
        (← Predicate.fromJson? (← j.getObjVal? "b"))
  | .ok "proj" =>
      return .proj (← Predicate.fromJson? (← j.getObjVal? "a"))
        (← Lean.fromJson? (← j.getObjVal? "key"))
  | .ok "app" =>
      return .app (← Predicate.fromJson? (← j.getObjVal? "f"))
        (← Predicate.fromJson? (← j.getObjVal? "a"))
  | .ok "lam" => return .lam (← Predicate.fromJson? (← j.getObjVal? "body"))
  | .ok "boundVar" => return .boundVar (← Lean.fromJson? (← j.getObjVal? "i"))
  | .ok "cast" =>
      let refs ← (← (← j.getObjVal? "refs").getArr?).toList.mapM Predicate.fromJson?
      return .cast (← Predicate.fromJson? (← j.getObjVal? "v")) refs
  | _ => throw s!"unknown Predicate: {j.compress}"

instance : ToJson Predicate := ⟨Predicate.toJson⟩
instance : FromJson Predicate := ⟨Predicate.fromJson?⟩

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

`CompactTy` is the merge model's mirror of `CompactType` (`CclFormal/Merge.lean`), and this codec is
the contract `tests/differential_oracle.rs` serializes a real `CompactType` to. The two abstractions
the model makes are applied *by the encoder*, so the wire carries only what the model can express:
the domain slot is `some d` for a single alternative and `null` for two or more, and a conflicted
slot's domain payload is `null` because coalesce reads it only for a diagnostic. Variable identities
and
history slots have no field — the model drops both. -/

def KindMerge.toWire : KindMerge → String
  | .data => "data"
  | .compute => "compute"
  | .conflict => "conflict"
  | .unknown => "unknown"

def KindMerge.fromWire : String → Except String KindMerge
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

namespace CompactTy

partial def toJson : CompactTy → Json
  | .mk atoms recF varT fn refinements =>
      let mapJson : List (FieldKey × CompactTy) → Json := fun m =>
        Json.arr (m.map fun (k, w) => Json.arr #[Lean.toJson k, toJson w]).toArray
      Json.mkObj
        [("atoms", Json.arr (atoms.map Atom.toJson).toArray),
         ("rec", match recF with | none => Json.null | some m => mapJson m),
         ("var", match varT with | none => Json.null | some m => mapJson m),
         ("fn", match fn with
                | none => Json.null
                | some (k, d, cod) =>
                    Json.mkObj [("kind", Lean.toJson k.toWire),
                      -- One domain, not a list: the slot holds one position
                      -- (`compact.rs`, `CompactFun::domain`).
                      ("dom", toJson d),
                      ("cod", toJson cod)]),
         ("refinements", match refinements with
                    | none => Json.null
                    | some ps => Json.arr (ps.map Lean.toJson).toArray)]

mutual

partial def fromJson? (j : Json) : Except String CompactTy := do
  let atoms ← (← (← j.getObjVal? "atoms").getArr?).toList.mapM Atom.fromJson?
  let recF ← optMap (← j.getObjVal? "rec")
  let varT ← optMap (← j.getObjVal? "var")
  let fn ← match ← j.getObjVal? "fn" with
    | Json.null => pure none
    | f => do
      let k ← KindMerge.fromWire (← (← f.getObjVal? "kind").getStr?)
      let d ← fromJson? (← f.getObjVal? "dom")
      let cod ← fromJson? (← f.getObjVal? "cod")
      pure (some (k, d, cod))
  let refinements ← match ← j.getObjVal? "refinements" with
    | Json.null => pure none
    | c => some <$> Lean.fromJson? c
  return .mk atoms recF varT fn refinements

/-- A `null`-or-array keyed map: the `Option (List (FieldKey × CompactTy))` slots. -/
partial def optMap (j : Json) : Except String (Option (List (FieldKey × CompactTy))) := do
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

end CompactTy

instance : ToJson CompactTy := ⟨CompactTy.toJson⟩
instance : FromJson CompactTy := ⟨CompactTy.fromJson?⟩

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
private def cRoundTrips (t : CompactTy) : Bool :=
  match (CompactTy.fromJson? (CompactTy.toJson t) : Except String CompactTy) with
  | .ok t' => CompactTy.equiv t t'
  | .error _ => false

-- `none` refinements (no contribution) and `some []` (a value guaranteeing nothing)
-- are distinct on the wire, which is the whole point of the slot's sentinel.
#guard cRoundTrips (.mk [] none none none none)
#guard cRoundTrips (.mk [] none none none (some []))
#guard !CompactTy.equiv (.mk [] none none none none) (.mk [] none none none (some []))
#guard cRoundTrips (.mk [.prim .int, .txn, .uintRange 3, .source "s"] none none none
  (some [.binop "eq" .elem (.litInt 1)]))
-- Every slot at once, including a conflicted kind, whose domain rides along like any other.
#guard cRoundTrips (.mk [.prim .bool]
  (some [(.idx 0, .mk [.prim .int] none none none (some []))])
  (some [(.name "tag", .mk [] none none none none)])
  (some (.conflict, .mk [] none none none none, .mk [.prim .string] none none none (some [])))
  (some []))
#guard cRoundTrips (.mk [] none none
  (some (.unknown, .mk [.prim .int, .prim .bool] none none none (some []),
    .mk [] (some []) none none none)) (some []))

end CclFormal
