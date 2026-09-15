import R2XiFirstPaid

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

#check @WuPaper.RMapMSigma.original_lemma61
#print axioms WuPaper.RMapMSigma.original_lemma61
#check @WuPaper.RMapMMatrix.source66_change_of_variables
#print axioms WuPaper.RMapMMatrix.source66_change_of_variables
#check @WuPaper.RMapMMatrix.source67_change_of_variables
#print axioms WuPaper.RMapMMatrix.source67_change_of_variables
#check @WuPaper.RMapMMatrix.source68_change_of_variables
#print axioms WuPaper.RMapMMatrix.source68_change_of_variables
#check @WuPaper.RMapMMatrix.original_four_rows_qualified
#print axioms WuPaper.RMapMMatrix.original_four_rows_qualified
#check @WuPaper.RMapMMatrix.original_five_rows_qualified
#print axioms WuPaper.RMapMMatrix.original_five_rows_qualified
#check @Wu2008DoubleSieve.wuImprovementLimit_firstFunctionalGain_source
#print axioms Wu2008DoubleSieve.wuImprovementLimit_firstFunctionalGain_source
#check @Wu04FirstPaid.publication_with_slack
#print axioms Wu04FirstPaid.publication_with_slack
#check @Wu04FirstCertificate.cost_paid
#print axioms Wu04FirstCertificate.cost_paid
#check @Wu04FirstPaid.debit_le_slack
#print axioms Wu04FirstPaid.debit_le_slack
