import Lean
import Lean.Util.FoldConsts
import WR2ClassicalCertificate
import W01ContinuousRoot
import W03Root
import W13Root
import W14AcceptedThreshold
import W15AcceptedThreshold
import W17ParentFullTypes
import WE10MajorAcceptedTotal
import WRMapMMatrixProbe
import WRMapMMatrixRoot
import WRecoveredFirstComparison
import WSrcFifthAnalyticInstance
import WSrcFourBudgetVerified
import WSrcFourEnclosureCone
import WSrcFourEnclosureFullTypes
import WSrcGridAccepted
import WSrcSingleGridInstance
import WSrcSingleRoot
import WSrcSixthGainRoot
import WSrcSixthGridInstance
import Wu2008Research
open Lean
set_option maxHeartbeats 40000000 in
run_cmd do
  let env ← Lean.getEnv
  let modules ← Lean.Elab.Command.liftIO <| IO.FS.readFile "/tmp/wu-shared-singular-series-v1/modules.txt"
  let localSet : Std.HashSet String := (modules.splitOn "\n").foldl (fun s n => s.insert n) {}
  let targets : Array Name := #[(Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "SwitchingPrinciple") "prod_one_sub_ge_one_sub_sum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "SwitchingPrinciple") "sum_sq_recip_primes_ge_three_le_half")]
  for n in targets do
    unless env.contains n do
      throwError "Missing target {n}"
  let mut rows : Array Json := #[]
  let mut scanned : Nat := 0
  let mut moduleCount : Nat := 0
  for idx in [:env.header.moduleNames.size] do
    let owner := env.header.moduleNames[idx]!.toString
    if localSet.contains owner then
      moduleCount := moduleCount + 1
      for ci in env.header.moduleData[idx]!.constants do
        scanned := scanned + 1
        let used := ci.getUsedConstantsAsSet
        for n in targets do
          if used.contains n then
            rows := rows.push <| Json.mkObj [
              ("target",toJson n.toString),("user",toJson ci.name.toString),
              ("module",toJson owner)]
  unless moduleCount == 4151 do
    throwError "Incomplete research module coverage {moduleCount}"
  let payload := Json.mkObj [("modules",toJson moduleCount),
    ("constants_scanned",toJson scanned),("incoming",Json.arr rows)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/wu-shared-singular-series-v1/helper-incoming.json" payload.compress
