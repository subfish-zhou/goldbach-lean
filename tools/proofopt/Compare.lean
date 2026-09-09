import Lean

/-! Exact compiled declaration preservation, separate from candidate fingerprints. -/
open Lean

unsafe def loadInfos (regions : IO.Ref (Array CompactedRegion)) (path : String) :
    IO (Std.HashMap String ConstantInfo) := do
  let mut files : Array System.FilePath := #[path]
  for suffix in ["server", "private"] do
    let p : System.FilePath := path ++ "." ++ suffix
    if ← p.pathExists then files := files.push p
  let mut out : Std.HashMap String ConstantInfo := {}
  for file in files do
    let (data, region) ← CompactedRegion.read (α := ModuleData) file (← regions.get)
    regions.modify (·.push region)
    for ci in data.constants do
      if let some old := out[ci.name.toString]? then
        unless old.name == ci.name do throw <| IO.userError "ambiguous serialized declaration name"
      out := out.insert ci.name.toString ci
  return out

def declarationKind : ConstantInfo → Nat
  | .axiomInfo _ => 0
  | .defnInfo _ => 1
  | .thmInfo _ => 2
  | .opaqueInfo _ => 3
  | .quotInfo _ => 4
  | .inductInfo _ => 5
  | .ctorInfo _ => 6
  | .recInfo _ => 7

unsafe def main (args : List String) : IO Unit := do
  let [before, after, namesPath] := args | throw <| IO.userError "expected old.olean new.olean names.txt"
  -- Separate compilations can reuse compacted base addresses. Only sidecar
  -- regions of the SAME artifact may share a relocation table.
  let oldRegions ← IO.mkRef (#[] : Array CompactedRegion)
  let newRegions ← IO.mkRef (#[] : Array CompactedRegion)
  let old ← loadInfos oldRegions before
  let new ← loadInfos newRegions after
  let mut count := 0
  let mut definitions := 0
  let mut seen : Std.HashSet String := {}
  for raw in (← IO.FS.readFile namesPath).splitOn "\n" do
    let name := raw.trimAscii.toString
    if name.isEmpty then continue
    unless !seen.contains name do throw <| IO.userError s!"duplicate requested name: {name}"
    seen := seen.insert name
    let some a := old[name]? | throw <| IO.userError s!"baseline declaration absent: {name}"
    let some b := new[name]? | throw <| IO.userError s!"candidate declaration absent: {name}"
    unless a.name == b.name && a.type == b.type && a.levelParams == b.levelParams do
      throw <| IO.userError s!"TYPE_OR_UNIVERSE_CHANGED {name}"
    unless declarationKind a == declarationKind b do throw <| IO.userError s!"DECLARATION_KIND_CHANGED {name}"
    if a.isDefinition || (match a with | .opaqueInfo _ => true | _ => false) then
      let some av := a.value? (allowOpaque := true) | throw <| IO.userError s!"old value unavailable: {name}"
      let some bv := b.value? (allowOpaque := true) | throw <| IO.userError s!"new value unavailable: {name}"
      unless av == bv do throw <| IO.userError s!"DEFINITION_VALUE_CHANGED {name}"
      definitions := definitions + 1
    IO.println s!"PRESERVED {name}"
    count := count + 1
  unless count > 0 do throw <| IO.userError "empty declaration inventory"
  IO.println s!"PROOFOPT_PRESERVATION_PASS declarations={count} definitions={definitions}"
