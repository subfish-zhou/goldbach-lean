-- UNCOMPILED metadata probe; no deletion or proof acceptance is performed.
import Lean
import Lean.Util.FoldConsts
@@MODULE_IMPORTS@@

open Lean
namespace CandidateConstantUseAudit

private def lastString : Name → String
  | .str _ s => s
  | _ => ""

set_option maxHeartbeats 40000000 in
run_cmd do
  let env ← Lean.getEnv
  if env.header.isModule then
    throwError "Constant-use census requires a non-module environment"
  let requested : Array (String × String) := @@REQUESTED@@
  let expectedModules : Array String := @@LOCAL_MODULES@@
  let scanModules : Array String := @@SCAN_MODULES@@
  let moduleNames := env.header.moduleNames
  let importedSet : Std.HashSet String := moduleNames.foldl (fun s n => s.insert n.toString) {}
  for m in expectedModules do
    unless importedSet.contains m do
      throwError "Missing research module in imported environment: {m}"
  let localModules : Std.HashSet String := expectedModules.foldl (fun s n => s.insert n) {}
  let wanted : Std.HashMap String String := requested.foldl (fun s p => s.insert p.1 p.2) {}
  if wanted.size != requested.size then
    throwError "Duplicate candidate basename"
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
  let scanSet : Std.HashSet String := scanModules.foldl (fun s n => s.insert n) {}
  for m in scanModules do
    unless localModules.contains m do
      throwError "Assigned scan module not imported: {m}"
  let scanDecls := localDecls.filter (fun (_, _, m) => scanSet.contains m)
  let mut resolved : Std.HashMap String (Array Name) := {}
  for (n, ci, m) in localDecls do
    if let some expected := wanted[lastString n]? then
      if m == expected then
        match ci with
        | .thmInfo _ =>
          let prior := resolved[lastString n]?.getD #[]
          resolved := resolved.insert (lastString n) (prior.push n)
        | _ => throwError "Candidate resolved to non-theorem: {n}"
  let mut targets : Std.HashSet Name := {}
  for (base, _) in requested do
    let names := resolved[base]?.getD #[]
    if names.size != 1 then
      throwError "Candidate {base} resolved to {names.size} constants"
    targets := targets.insert names[0]!
  let mut incoming : Std.HashMap Name (Array Json) := {}
  let mut scannedValues : Nat := 0
  for (n, ci, m) in scanDecls do
    if ci.hasValue (allowOpaque := true) then
      scannedValues := scannedValues + 1
    -- Includes proof and opaque values, not just written types. It also
    -- accounts for constructor/recursor names through the official API.
    for dependency in ci.getUsedConstantsAsSet.toList do
      if targets.contains dependency then
        let users := incoming[dependency]?.getD #[]
        let row := Json.mkObj [("name", toJson n.toString), ("module", toJson m)]
        incoming := incoming.insert dependency (users.push row)
  let mut rows : Array Json := #[]
  for (base, m) in requested do
    let n := (resolved[base]?.getD #[])[0]!
    let users := incoming[n]?.getD #[]
    rows := rows.push <| Json.mkObj [
      ("basename", toJson base), ("module", toJson m), ("name", toJson n.toString),
      ("privateRuntimeName", toJson (n.toString.startsWith "_private.")),
      ("incomingCount", toJson users.size), ("incomingUsers", .arr users)]
  let payload := Json.mkObj [
    ("schema", toJson "wu-candidate-constant-use-v2-raw-module-data"),
    ("status", toJson "ELABORATED_USE_INVENTORY_NOT_RETIREMENT_OR_PROOF_ACCEPTANCE"),
    ("requestedCount", toJson requested.size),
    ("expectedResearchModules", toJson expectedModules.size),
    ("assignedScanModules", toJson scanModules),
    ("constantInventory", toJson "unmerged private-inclusive ModuleData.constants; provenance from raw module index"),
    ("importedResearchConstants", toJson localDecls.size),
    ("scannedResearchConstants", toJson scanDecls.size),
    ("scannedValuesIncludingTheoremsAndOpaque", toJson scannedValues),
    ("scope", toJson "all research constant types and opaque-inclusive values; direct constant references"),
    ("candidates", Json.arr rows)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile @@OUTPUT_PATH@@ payload.compress

end CandidateConstantUseAudit
