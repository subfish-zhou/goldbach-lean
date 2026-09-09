import Lean

/-! Read-only, version-pinned .olean declaration index. Hashes are candidate keys,
not kernel equality certificates. No environment import and no proof pretty-print. -/
open Lean
namespace ProofOpt

structure Fingerprint where
  exact : UInt64
  shape : UInt64
  nodes : Nat
  deriving Inhabited

-- Tagged, length-aware structural hashing. Exact and shape each have a UInt64
-- stream; they are non-cryptographic candidate keys, not Lean Expr.hash.
def combine (seed : UInt64) (xs : Array UInt64) : UInt64 :=
  xs.foldl (fun h x => mixHash h x) (mixHash seed xs.size.toUInt64)

def nameKey : Name → UInt64
  | .anonymous => 17
  | .str p s => combine 19 #[nameKey p, hash s, s.utf8ByteSize.toUInt64]
  | .num p n => combine 23 #[nameKey p, hash n]

def levelKey : Level → UInt64
  | .zero => 29
  | .succ l => combine 31 #[levelKey l]
  | .max a b => combine 37 #[levelKey a, levelKey b]
  | .imax a b => combine 41 #[levelKey a, levelKey b]
  | .param n => combine 43 #[nameKey n]
  | .mvar n => combine 47 #[nameKey n.name]

def binderKey : BinderInfo → UInt64
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

unsafe abbrev Cache := PtrMap Expr Fingerprint

unsafe def fingerprint (cache : IO.Ref Cache) (e : Expr) : IO Fingerprint := do
  if let some r := (← cache.get).find? e then return r
  let (tag, fields, shapeFields, children) :
      UInt64 × Array UInt64 × Array UInt64 × Array Expr := match e with
    | .bvar i => (101, #[hash i], #[hash i], #[])
    | .fvar i => (103, #[nameKey i.name], #[nameKey i.name], #[])
    | .mvar i => (107, #[nameKey i.name], #[nameKey i.name], #[])
    | .sort l => (109, #[levelKey l], #[], #[])
    | .const n ls => (113, #[nameKey n] ++ ls.toArray.map levelKey, #[], #[])
    | .app f a => (127, #[], #[], #[f, a])
    | .lam _ t b bi => (131, #[binderKey bi], #[binderKey bi], #[t, b])
    | .forallE _ t b bi => (137, #[binderKey bi], #[binderKey bi], #[t, b])
    | .letE _ t v b nd => (139, #[if nd then 1 else 0], #[if nd then 1 else 0], #[t, v, b])
    | .lit (.natVal n) => (149, #[hash n], #[], #[])
    | .lit (.strVal s) => (151, #[hash s, s.utf8ByteSize.toUInt64], #[], #[])
    | .mdata _ b => (0, #[], #[], #[b])
    | .proj n i b => (157, #[nameKey n, hash i], #[hash i], #[b])
  let mut exactChildren := #[]
  let mut shapeChildren := #[]
  let mut nodes := 1
  let mut only : Fingerprint := default
  for child in children do
    let r ← fingerprint cache child
    only := r
    exactChildren := exactChildren.push r.exact
    shapeChildren := shapeChildren.push r.shape
    nodes := nodes + r.nodes
  let r := if tag == 0 then only else
    { exact := combine tag (fields ++ exactChildren)
      shape := combine (tag + 1009) (shapeFields ++ shapeChildren)
      nodes := nodes }
  cache.modify (·.insert e r)
  return r

def children : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ t b _ | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

-- A DAG walk per declaration; dependency sets are not stored at every subtree.
unsafe def dependencies (root : Expr) : Array String := Id.run do
  let mut seen : PtrSet Expr := mkPtrSet
  let mut names : Std.HashSet Name := {}
  let mut stack := #[root]
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .const n _ => names := names.insert n
    | .proj n _ _ => names := names.insert n
    | _ => pure ()
    stack := stack ++ children e
  return (names.toArray.map toString).qsort (· < ·)

partial def conclusionHead : Expr → Option String
  | .forallE _ _ b _ | .mdata _ b | .letE _ _ _ b _ => conclusionHead b
  | .app f _ => conclusionHead f
  | .const n _ => some n.toString
  | .sort _ => some "<sort>"
  | .bvar _ => some "<bound-variable>"
  | .proj n i _ => some s!"{n}.<projection:{i}>"
  | _ => none

-- Explicitly bounded rendering; full original Expr.toString is opt-in.
def brief : Nat → Expr → String
  | 0, _ => "…"
  | fuel+1, e => match e with
    | .forallE n t b bi => s!"forall[{binderKey bi}] {n} : {brief fuel t}, {brief fuel b}"
    | .lam n t b bi => s!"fun[{binderKey bi}] {n} : {brief fuel t} => {brief fuel b}"
    | .app f a => s!"({brief fuel f} {brief fuel a})"
    | .const n _ => n.toString
    | .bvar i => s!"#{i}"
    | .sort l => s!"Sort {l}"
    | .mdata _ b => brief fuel b
    | .letE n t v b _ => s!"let {n} : {brief fuel t} := {brief fuel v}; {brief fuel b}"
    | .proj n i b => s!"{n}.{i}({brief fuel b})"
    | .fvar n => s!"fvar:{n.name}"
    | .mvar n => s!"mvar:{n.name}"
    | .lit (.natVal n) => toString n
    | .lit (.strVal s) => s!"{repr (s.take 80).toString}"

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def internalReason (ci : ConstantInfo) : Option String :=
  if isPrivateName ci.name then some "private-name"
  else if ci.name.isInternalDetail then some "lean-internal-detail-name"
  else if kind ci == "recursor" then some "generated-recursor"
  else if ["recOn", "casesOn", "brecOn", "below", "ibelow", "noConfusion", "noConfusionType",
      "injEq", "inj", "sizeOf_spec", "ctorIdx", "toCtorIdx"].contains ci.name.getString! then some "generated-helper-name"
  else none

def js (s : String) : Json := Json.str s
def ja (xs : Array String) : Json := Json.arr (xs.map js)
def jo (s : Option String) : Json := s.map js |>.getD Json.null

def hashText (h : UInt64) : String := s!"lean4-struct-v1:{h}"
def shapeText (h : UInt64) : String := s!"lean4-shape-v1:{h}"

unsafe def emitDeclaration (out : IO.FS.Stream) (cache : IO.Ref Cache)
    (mod : String) (full : Bool) (ci : ConstantInfo) : IO Unit := do
  let t ← fingerprint cache ci.type
  let value := ci.value? (allowOpaque := true)
  let p ← value.mapM (fingerprint cache)
  let reason := internalReason ci
  let row := Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("module", js mod), ("name", js ci.name.toString),
    ("kind", js (kind ci)), ("type_hash", js (hashText t.exact)),
    ("type_shape_hash", js (shapeText t.shape)), ("conclusion_head", jo (conclusionHead ci.type)),
    ("level_params", ja (ci.levelParams.toArray.map toString)),
    ("proof_hash", jo (p.map fun f => hashText f.exact)),
    ("proof_nodes", (p.map fun f => toJson f.nodes).getD Json.null),
    ("direct_deps", ja (value.map dependencies |>.getD #[])),
    ("type_deps", ja (dependencies ci.type)),
    ("is_internal", toJson reason.isSome), ("internal_reason", jo reason),
    ("value_available", toJson value.isSome),
    ("type_summary", js ((brief 5 ci.type).take 1200).toString),
    ("type_string", if full then js (toString ci.type) else Json.null),
    ("source_range", Json.null), ("source_range_status", js "unavailable:not-reading-ilean")]
  out.putStrLn row.compress

-- Keep all references to compacted data inside this noinline frame. The caller
-- frees regions only after this frame, the map and Expr cache have been destroyed.
@[noinline] unsafe def emitModule (out err : IO.FS.Stream)
    (regions : IO.Ref (Array CompactedRegion)) (mod path : String) (full : Bool) : IO Unit := do
  unless path.endsWith ".olean" do
    throw <| IO.userError "input must be the base .olean (sidecars are discovered automatically)"
  let mut files : Array System.FilePath := #[path]
  for suffix in ["server", "private"] do
    let p : System.FilePath := path ++ "." ++ suffix
    if ← p.pathExists then files := files.push p
  -- Same ordered loading protocol as readModuleDataParts, but register each
  -- region immediately so a corrupt/missing later sidecar cannot leak earlier parts.
  let mut parts : Array (ModuleData × CompactedRegion) := #[]
  for file in files do
    let part ← CompactedRegion.read (α := ModuleData) file (← regions.get)
    regions.modify (·.push part.2)
    parts := parts.push part
  let mut infos : Std.HashMap Name ConstantInfo := {}
  for (data, _) in parts do
    for ci in data.constants do infos := infos.insert ci.name ci
  let cache ← IO.mkRef (mkPtrMap : Cache)
  let sorted := infos.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (_, ci) in sorted do emitDeclaration out cache mod full ci
  out.flush
  err.putStrLn s!"module={mod} declarations={sorted.size} parts={parts.size} cached_nodes={Std.HashMap.size (← cache.get)} release_regions={parts.size}"

unsafe def runModule (out err : IO.FS.Stream) (mod path : String) (full : Bool) : IO Unit := do
  let regions ← IO.mkRef (#[] : Array CompactedRegion)
  try emitModule out err regions mod path full
  finally
    let rs ← regions.swap #[]
    for r in rs.reverse do r.free

def readManifest (path : String) : IO (Array (String × String)) := do
  let mut pairs := #[]
  for raw in (← IO.FS.readFile path).splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let [mod, path] := line.splitOn "\t"
      | throw <| IO.userError "manifest expects module<TAB>absolute.olean"
    pairs := pairs.push (mod, path)
  return pairs

unsafe def mainImpl (args : List String) : IO Unit := do
  let full := args.contains "--type-string"
  let args := args.filter (· != "--type-string")
  let pairs ← match args with
    | ["--manifest", input] => readManifest input
    | [] => throw <| IO.userError "usage: Extract.lean --manifest INPUT.tsv [--type-string] | MODULE=PATH.olean ..."
    | xs => xs.toArray.mapM fun s => do
      let [mod, path] := s.splitOn "="
        | throw <| IO.userError "expected MODULE=PATH.olean"
      return (mod, path)
  let out ← IO.getStdout
  let err ← IO.getStderr
  for (mod, path) in pairs do runModule out err mod path full
end ProofOpt

unsafe def main (args : List String) : IO Unit := ProofOpt.mainImpl args
