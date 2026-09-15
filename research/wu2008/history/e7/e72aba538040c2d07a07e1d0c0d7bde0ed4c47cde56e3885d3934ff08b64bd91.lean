import WRMapMMatrixSelectedChange
import WRMapMMatrixDomainGap

namespace WuPaper.RMapMMatrix

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.RMapMMatrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.RMapMMatrix
