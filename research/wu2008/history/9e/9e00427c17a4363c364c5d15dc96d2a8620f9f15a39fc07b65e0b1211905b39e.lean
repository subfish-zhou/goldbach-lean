import RMapMMatrixInspect

open Wu2008DoubleSieve

#print MotherPair.feedbackLower
#print MotherPair.feedbackUpper
#print MotherPair.feedbackPole
#print MotherPair.feedbackFactor
#print MotherPair.feedbackKernel
#print MotherPair.feedbackDensity
#print MotherPair.Term
#print SecondFunctionalParameters.MotherAdmissible

run_cmd do
  for (name, ci) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `Wu2008DoubleSieve.MotherPair &&
        (name.toString.contains "feedback" || name.toString.contains "Feedback") then
      if ci.isTheorem then
        Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
