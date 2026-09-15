import SrcNineRoot

namespace WuSource.SrcNine.Analytic

#print Wu2008DoubleSieve.SecondFunctionalCoupled.kernel
#print Wu2008DoubleSieve.SecondFunctionalCoupled.values
#check @Wu2008DoubleSieve.SecondFunctionalCoupled.jointSup_bounds
#print Wu2008DoubleSieve.SecondFunctionalCoupled.jointSup
#print Wu2008DoubleSieve.omega3XIntegral
#print Wu2008DoubleSieve.omega3XIntegralEnvelope
#print Wu2008DoubleSieve.HighNonunitLegal.K20
#print Wu2008DoubleSieve.HighNonunitLegal.K21
#print Wu2008DoubleSieve.HighNonunitLegal.D20
#print Wu2008DoubleSieve.HighNonunitLegal.D21
#print Wu2008DoubleSieve.HighUnit.J20
#print Wu2008DoubleSieve.HighUnit.J21

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Wu2008DoubleSieve.SecondFunctionalCoupled." ||
        name.toString.startsWith "Wu2008DoubleSieve.SecondFunctionalJointTail." ||
        name.toString.startsWith "Wu2008DoubleSieve.HighNonunitLegal." ||
        name.toString.startsWith "Wu2008DoubleSieve.LowerTripleSourceK." then
      if !name.toString.contains '_' then
        pure ()
      unless name.toString.contains "proof" || name.toString.contains "match" ||
          name.toString.contains "eq_" do
        logInfo m!"{name} : {info.type}"

end WuSource.SrcNine.Analytic
