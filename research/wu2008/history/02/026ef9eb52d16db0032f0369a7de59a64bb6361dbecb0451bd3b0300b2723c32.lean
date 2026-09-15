import SrcSixthGainRoot
import BuchstabCountFinal

open Wu2008DoubleSieve
#print wuSourceBox
#print wuEventualImprovements
#print wuImprovementComparison
#print wuClosedEventualImprovements
#print truncatedSixthLowerAdmissibleRegion
#print truncatedSixthLowerRegion
#print truncatedSixthLowerPairs
#print truncatedSixthMass
#print wuBoxPhiLE
#check Real.rpow_le_rpow_left_iff
#check Real.rpow_le_rpow_iff_of_base_gt_one
#check Real.rpow_le_rpow_left_iff_of_base_gt_one
#check Real.rpow_le_rpow_of_exponent_le
#check Real.rpow_lt_rpow_left_iff
#check HighCross.omega1_eq_twice_phi

open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if (name.toString.startsWith "BuchstabCount." ||
        name.toString.startsWith "Wu2008DoubleSieve.truncatedSixthLower") &&
        (name.toString.splitOn "._").length == 1 then
      logInfo m!"{name} : {info.type}"
