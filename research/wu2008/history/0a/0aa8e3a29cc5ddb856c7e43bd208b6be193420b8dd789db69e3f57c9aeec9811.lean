import W09PaidRowsV2
import WSourceClosureBudget
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Wu2008DoubleSieve" &&
        (s.contains "firstFunctional" || s.contains "SecondFunctionalMother." ||
         s.contains "SecondFunctionalCoupled." || s.contains "MotherPair.") &&
        (s.endsWith "mother" || s.endsWith "source" || s.endsWith "finite" ||
         s.endsWith "upper" || s.contains "Gain" || s.endsWith "Admissible") &&
        !s.contains "_proof" && !s.contains "match_" && !s.contains "._") then
      logInfo m!"{n} : {c.type}"

namespace WuSource.SrcSingle
open Wu2008DoubleSieve
#print boxSquaredPrefixes
#check @wu_omega_weighted_finite
#check @SingleUpperHIntegral.kernel_integrable
#check @SingleUpperHIntegral.windowGain
#check @wuImprovementLimit_div_intervalIntegrable
#check @wuImprovementLimit_intervalIntegrable
#check @SingleUpperClassicalLimit.Gdelta_close
end WuSource.SrcSingle
