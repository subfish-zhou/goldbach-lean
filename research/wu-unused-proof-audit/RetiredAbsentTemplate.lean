-- UNCOMPILED metadata probe; no deletion or proof acceptance is performed.
import Lean
import Lean.Util.FoldConsts
@@MODULE_IMPORTS@@

open Lean
namespace CandidateConstantUseAudit

set_option maxHeartbeats 40000000 in
run_cmd do
  let env ← Lean.getEnv
  if env.header.isModule then
    throwError "Constant-use census requires a non-module environment"
  let requested : Array (String × String) := @@REQUESTED@@
  let expectedModules : Array String := @@LOCAL_MODULES@@
  let moduleNames := env.header.moduleNames
  let importedSet : Std.HashSet String := moduleNames.foldl (fun s n => s.insert n.toString) {}
  for m in expectedModules do
    unless importedSet.contains m do
      throwError "Missing research module in imported environment: {m}"
  let localModules : Std.HashSet String := expectedModules.foldl (fun s n => s.insert n) {}
  let wanted : Std.HashMap String String := requested.foldl (fun s p => s.insert p.1 p.2) {}
  if wanted.size != requested.size then
    throwError "Duplicate retirement runtime name"
  if env.header.moduleData.size != moduleNames.size then
    throwError "Module names/data length mismatch"
  let mut localDecls : Array (Name × ConstantInfo × String) := #[]
  for idx in [:moduleNames.size] do
    let m := moduleNames[idx]!.toString
    if localModules.contains m then
      let imp := env.header.modules[idx]!
      unless imp.importAll && imp.hasData do
        throwError "Research module lacks private-inclusive data: {m}"
      let data := env.header.moduleData[idx]!
      if data.constNames.size != data.constants.size then
        throwError "Module constant name/data length mismatch: {m}"
      let mut seen : Std.HashSet Name := {}
      for cidx in [:data.constants.size] do
        let ci := data.constants[cidx]!
        let n := data.constNames[cidx]!
        unless n == ci.name do
          throwError "Module constant name/data mismatch: {m} / {n}"
        if seen.contains n then
          throwError "Duplicate constant within one module: {m} / {n}"
        seen := seen.insert n
        localDecls := localDecls.push (n, ci, m)
  for (_, owner) in requested do
    unless localModules.contains owner do
      throwError "Retirement target owner is outside the imported research scope: {owner}"
  for (n, _, _) in localDecls do
    if wanted.contains n.toString then
      throwError "Retired declaration survived: {n}"
  let payload := Json.mkObj [
    ("schema", toJson "wu-retired-declaration-absence-v1"),
    ("status", toJson "RAW_PRIVATE_INCLUSIVE_RETIREMENT_ABSENCE_NOT_PROOF_ACCEPTANCE"),
    ("requestedCount", toJson requested.size),
    ("absentCount", toJson requested.size),
    ("expectedResearchModules", toJson expectedModules.size),
    ("scannedResearchConstants", toJson localDecls.size)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile @@OUTPUT_PATH@@ payload.compress
end CandidateConstantUseAudit
