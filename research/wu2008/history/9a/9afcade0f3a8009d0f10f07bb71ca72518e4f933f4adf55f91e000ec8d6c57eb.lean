import SrcSingleAnalyticOmegaIntegral

namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve
#print secondFunctionalMotherGammaSum
#print secondFunctionalMotherGammaLocal
#check @omega3_source_integral_upper
#check @SecondFunctionalClassicalAlgebra.coefficient_eq
#check @Wu08OriginalPsiRecovery.coupledBase_eq_original_logs
#print MotherPair.classicalIntegral

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve." &&
        (s.contains "secondFunctional" || s.contains "FourthRow" ||
          s.contains "MotherPair." || s.contains "omega3" ||
          s.contains "HighSix.Omega3Upper.") &&
        (s.endsWith "upper" || s.endsWith "bound" || s.endsWith "bounds" ||
          s.endsWith "paid" || s.endsWith "density" || s.endsWith "support" ||
          s.endsWith "geometry") &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" then
      logInfo m!"{n} : {c.type}"
end WuSource.SrcSingle.Analytic
