import SrcNineAnalyticIntegralSplit

namespace WuSource.SrcNine.Analytic
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "LiLiuPrereqBuchstab." then
      unless name.toString.contains "proof" || name.toString.contains "match" do
        logInfo m!"{name} : {info.type}"
#print LiLiuPrereqBuchstab.approx._f
#check @Wu2008DoubleSieve.SecondFunctionalJointTail.mother_unit_pair_zero
#check @Wu2008DoubleSieve.SecondFunctionalJointTail.cube_legal_of_tail
#check @csSup_add
#check @csSup_image_add
#check @Real.sSup_add
end WuSource.SrcNine.Analytic
