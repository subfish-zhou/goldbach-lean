import Lean
import Lean.Util.FoldConsts
import WR2ClassicalCertificate
open Lean
set_option maxHeartbeats 40000000 in
run_cmd do
  let env ← Lean.getEnv
  let target := (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "AnalyticNumberTheory") "Sieve") "PanV3SquareMean") 0) "AnalyticNumberTheory") "Sieve") "lcm_inv_eq_gcd_div")
  unless env.contains target do
    throwError "Missing target {target}"
  let mut incoming : Array Json := #[]
  let mut scanned := 0
  for idx in [:env.header.moduleNames.size] do
    for ci in env.header.moduleData[idx]!.constants do
      scanned := scanned + 1
      if ci.getUsedConstantsAsSet.contains target then
        incoming := incoming.push <| Json.mkObj [
          ("name",toJson ci.name.toString),
          ("module",toJson env.header.moduleNames[idx]!.toString)]
  let payload := Json.mkObj [("target",toJson target.toString),
    ("constants_scanned",toJson scanned),("incoming",Json.arr incoming)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/wu-pan-shared-square-v1/private-incoming.json" payload.compress
