import SrcSingleRoot

namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve
#check @SingleUpperCounts.global_signed_bv
#check @SingleUpperCounts.source_count
#check @SingleUpperCounts.single_weighted_sum
#check @HighSix.double_masked_bv
#check @HighSix.thetaAtom
#check @HighSix.B6_sum
#print secondFunctionalMotherRHS
#print wuOmega1
#check @ordinaryRosser_upper_finite
#check @ordinaryRosser_lower_finite
#check @ordinaryRosser_upper_density_canonical_extended_local
#check @canonical_upper_extended_normalization_budget

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Wu2008DoubleSieve.FourthRowPhiOmega2." ||
        s.startsWith "Wu2008DoubleSieve.SecondFunctionalCoupled." ||
        s.startsWith "Wu2008DoubleSieve.secondFunctional_pair" ||
        s.startsWith "Wu2008DoubleSieve.HighSix.") &&
        (s.endsWith "upper" || s.endsWith "lower" || s.endsWith "paid" ||
          s.endsWith "scalarization" || s.endsWith "main" || s.endsWith "mass") &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" then
      logInfo m!"{n} : {c.type}"
end WuSource.SrcSingle.Analytic
