import SrcNineRoot

namespace WuSource.SrcNine.Analytic

#print Wu2008DoubleSieve.LowerTripleContinuous.D
#print Wu2008DoubleSieve.LowerTripleContinuous.K
#print Wu2008DoubleSieve.LowerTripleContinuous.G
#print Wu2008DoubleSieve.FourPrimeNonunit.legalK
#print Wu2008DoubleSieve.SecondFunctionalJointTail.massDomainFour
#print Wu2008DoubleSieve.SecondFunctionalJointTail.massDomain20
#print Wu2008DoubleSieve.SecondFunctionalJointTail.massDomain21
#print Wu2008DoubleSieve.HighNonunitLegal.G
#print Wu2008DoubleSieve.HighNonunitLegal.legal
#print Wu2008DoubleSieve.HighUnit.section20
#print Wu2008DoubleSieve.HighUnit.section21
#print Wu2008DoubleSieve.omega3XIntegralKernel

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Wu2008DoubleSieve.LowerTripleContinuous." ||
        name.toString.startsWith "Wu2008DoubleSieve.FourPrimeNonunit." ||
        name.toString.startsWith "LiLiuPrereqBuchstab.buchstab_" then
      unless name.toString.contains "proof" || name.toString.contains "match" ||
          name.toString.contains "._" || name.toString.contains "eq_" do
        logInfo m!"{name} : {info.type}"

end WuSource.SrcNine.Analytic
