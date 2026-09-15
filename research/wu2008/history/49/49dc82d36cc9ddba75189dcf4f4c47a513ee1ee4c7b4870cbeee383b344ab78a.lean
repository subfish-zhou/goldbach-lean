import WRMapMSigmaRoot
import WRMapMMatrixSelectedChange

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.toString.startsWith "Wu2008DoubleSieve.firstFunctionalGain" then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))

#check @intervalIntegral.integral_congr_uIoo
#check @intervalIntegral.integral_congr_ae
#check @MeasureTheory.integral_integral_swap
#check @MeasureTheory.IntegrableOn.mul_continuousOn
#check @ContinuousOn.integrableOn_Icc
#check @MeasureTheory.Integrable.mul_bdd
#check @intervalIntegral.integral_add
