import Lean
import WR2ClassicalCertificate
open Lean
set_option maxHeartbeats 40000000 in
run_cmd do
  let env ← Lean.getEnv
  let expectedText ← Lean.Elab.Command.liftIO <| IO.FS.readFile "/tmp/wu-final-type-duplicates-v1/modules.txt"
  let expected := ((expectedText.splitOn "\n").filter (· != "")).toArray
  let localSet : Std.HashSet String := expected.foldl (fun s n => s.insert n) {}
  let mut observed : Std.HashSet String := {}
  let mut groups : Std.HashMap Expr (Array (Name × String)) := {}
  let mut count := 0
  for idx in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[idx]!.toString
    if localSet.contains owner then
      observed := observed.insert owner
      let data := env.header.moduleData[idx]!
      for ci in data.constants do
        if let .thmInfo th := ci then
          count := count + 1
          let ty := th.type
          groups := groups.insert ty ((groups[ty]?.getD #[]).push (th.name, owner))
  unless observed.size == expected.size do
    throwError "Incomplete local module coverage: {observed.size}/{expected.size}"
  let mut rows : Array Json := #[]
  for (ty, entries) in groups do
    if entries.size > 1 then
      rows := rows.push <| Json.mkObj [
        ("type_hash_candidate_only", toJson ty.hash.toNat),
        ("members", Json.arr (entries.map fun (n,m) => Json.mkObj [
          ("name",toJson n.toString),("module",toJson m)]))]
  let result := Json.mkObj [
    ("status",toJson "TYPE_EQUALITY_CANDIDATES_ONLY_NO_REPLACEMENT_ACCEPTANCE"),
    ("modules",toJson observed.size),("theorems",toJson count),
    ("groups",Json.arr rows)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/wu-final-type-duplicates-v1/groups.json" result.compress
