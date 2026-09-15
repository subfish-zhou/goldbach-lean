import SrcSingleRoot

namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve
#print wuUpperCoefficient
#print boxTheta
#print convolutionSieveCount
#print HighSix.thetaAtom
#print wuOmega2
#print wuOmega2Sum
#check @sourceSieveCount_antitone
#check @wuUpperCoefficient_antitone
#print SecondFunctionalCoupled.actual_phi_ge_two

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Wu2008DoubleSieve." &&
        (s.contains "density" && s.contains "upper" ||
          s.contains "normalization" && s.contains "upper" ||
          s.contains "Phi" && s.endsWith "upper")) &&
        !s.contains "._" && !s.contains "_proof" && !s.contains ".match_" then
      logInfo m!"{n} : {c.type}"
end WuSource.SrcSingle.Analytic
