import SrcSingleAnalyticOmegaIntegral

namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve
#print fourthRowClassicalJ
#print ActualNineFeedback.coupledBase
#print ActualNineFeedback.coupledCostMass
#print SecondFunctionalSignedCore.classical
#check @SecondFunctionalSignedCore.classical_eq_triangles
#check @MotherPair.original_eq
#check @MotherPair.original_le_fixed
#check @gamma5Classical_masked_remainder_le
#check @MotherPair.gamma_eq_term
#print gamma5ClassicalMainMass
#print gamma5ClassicalLevel
#print gamma5ClassicalLabel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve.MotherPair." &&
        (s.contains "original" || s.contains "coprime" || s.contains "pair" ||
          s.contains "arithmetic" || s.contains "term") &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" &&
        !s.endsWith "eq_1" && !s.endsWith "eq_2" && !s.endsWith "eq_3" && !s.endsWith "eq_4" then
      logInfo m!"{n} : {c.type}"
end WuSource.SrcSingle.Analytic
