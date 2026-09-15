import WR2MatrixOriginalSystem

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Matrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

#check @WuPaper.RMapMMatrix.original_four_rows_qualified
#print axioms WuPaper.RMapMMatrix.original_four_rows_qualified
#check @WuPaper.RMapMMatrix.original_five_rows_qualified
#print axioms WuPaper.RMapMMatrix.original_five_rows_qualified
#check @Wu04Source.coefficient_eq_project
#print axioms Wu04Source.coefficient_eq_project
#check @Wu2008DoubleSieve.wuImprovementLimit_upper_antitone
#print axioms Wu2008DoubleSieve.wuImprovementLimit_upper_antitone
