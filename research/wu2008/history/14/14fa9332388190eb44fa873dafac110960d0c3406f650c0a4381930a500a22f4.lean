import SrcSingleAnalyticOmegaIntegral

namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve
#print fourthRowClassicalJ
#print ActualNineFeedback.coupledBase
#print ActualNineFeedback.coupledCostMass
#print SecondFunctionalCoupledFeedback.classical
#check @SecondFunctionalSignedCore.classical_eq_triangles
#check @gamma5Classical_masked_remainder_le
#print gamma5ClassicalMainMass
#print gamma5ClassicalLevel
#print Gamma5ClassicalLabel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in [``MotherPair.rectangle_mass, ``MotherPair.rect_sum,
      ``MotherPair.classical_original_upper, ``ordinaryRosser_upper_density_canonical_bounded_local] do
    if let some idx := env.getModuleIdxFor? n then
      logInfo m!"OWNER {n}: {env.header.moduleNames[idx]!}"
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve.MotherPair." &&
        (s.contains "original" || s.contains "coprime" || s.contains "pair" ||
          s.contains "arithmetic" || s.contains "term") &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" &&
        !s.endsWith "eq_1" && !s.endsWith "eq_2" && !s.endsWith "eq_3" && !s.endsWith "eq_4" then
      logInfo m!"{n} : {c.type}"
end WuSource.SrcSingle.Analytic
