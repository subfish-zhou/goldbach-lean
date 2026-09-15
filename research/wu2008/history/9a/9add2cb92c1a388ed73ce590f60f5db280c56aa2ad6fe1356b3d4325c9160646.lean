import RMapMMatrixKernelTypes

open Wu2008DoubleSieve
#print MotherPair.upperP
#print MotherPair.lowerQ
#print MotherPair.upperQ
#print MotherPair.Hratio
#print MotherPair.gainIntegral
#print MotherPair.gainRegion
#print MotherPair.gainKernel
#print MotherPair.FullHParameters
#print MotherPair.feedbackU
#print MotherPair.feedbackJac
#print MotherPair.gainBox
#check @MotherPair.feedback_fullH_identity

run_cmd do
  for (name, ci) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `Wu2008DoubleSieve.MotherPair &&
        (name.toString.contains "full" || name.toString.contains "Full" ||
          name.toString.contains "gainIntegral") then
      if ci.isTheorem then
        Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
