import Lean

/-!
Read compiled objects, not an elaborated namespace approximation. Each batch is
an isolated process so compacted regions cannot accumulate across the project.
No project module is recompiled and no imported extension is executed.
-/
open Lean

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

private def names (e : Expr) : Json := toJson (e.getUsedConstants.map Name.toString)

private def declaration (ci : ConstantInfo) : IO Json := do
  let value := ci.value? (allowOpaque := true)
  if ["definition", "theorem", "opaque"].contains (kind ci) && value.isNone then
    throw <| IO.userError s!"Required value missing: {ci.name}"
  let rules := match ci with
    | .recInfo r => r.rules.toArray.flatMap (fun (x : RecursorRule) => x.rhs.getUsedConstants)
    | _ => #[]
  return Json.mkObj [
    ("name", toJson ci.name.toString), ("kind", toJson (kind ci)),
    ("hasValue", toJson value.isSome), ("type", names ci.type),
    ("value", value.map names |>.getD (toJson (#[] : Array String))),
    ("recursorRHS", toJson (rules.map Name.toString))]

unsafe def extract (source object output : String) : IO Unit := do
  let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile source) source
  if messages.hasErrors then throw <| IO.userError s!"Invalid import header: {source}"
  let mut paths : Array System.FilePath := #[object]
  for suffix in [".server", ".private"] do
    let p := System.FilePath.mk (object ++ suffix)
    if ← p.pathExists then paths := paths.push p
  let mut parts ← readModuleDataParts paths
  let ir := (System.FilePath.mk object).withExtension "ir"
  let sig := (System.FilePath.mk object).withExtension "ir.sig"
  if ← sig.pathExists then
    if !(← ir.pathExists) then throw <| IO.userError s!"Missing IR companion: {ir}"
    parts := parts ++ (← readModuleDataParts #[sig, ir])
    paths := paths ++ #[sig, ir]
  let mut declarations := #[]
  let mut census : Array String := #[]
  let mut extra : Array String := #[]
  let mut compiledImports : Array String := #[]
  for (md, _) in parts do
    unless md.constNames == md.constants.map (·.name) do
      throw <| IO.userError s!"ModuleData.constNames mismatch: {object}"
    census := census ++ md.constNames.map Name.toString
    extra := extra ++ md.extraConstNames.map Name.toString
    compiledImports := compiledImports ++ md.imports.map (·.module.toString)
    for ci in md.constants do declarations := declarations.push (← declaration ci)
  IO.FS.writeFile output <| (Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("sourceImports", toJson (imports.map (·.module.toString))),
    ("compiledImports", toJson compiledImports),
    ("objectParts", toJson (paths.map System.FilePath.toString)),
    ("constNames", toJson census), ("extraConstNames", toJson extra),
    ("declarations", toJson declarations)]).compress

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [manifest] =>
    let rows := (← IO.FS.readFile manifest).splitOn "\n" |>.filter (· != "")
    for row in rows do
      match row.splitOn "\t" with
      | [source, object, output] => extract source object output
      | _ => throw <| IO.userError "Expected source TAB object TAB output"
  | _ => throw <| IO.userError "Usage: lake env lean --run tools/ProjectStructure.lean manifest.tsv"
