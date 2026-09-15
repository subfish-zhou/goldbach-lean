import Wu08TerminalAlignment

open Lean Elab Command
namespace WuPaper.RMapMFirst

#print Wu2008DoubleSieve.wuUpperCoefficient
#print Wu2008DoubleSieve.wuLowerCoefficient
#print Wu2008DoubleSieve.SingleUpperClassicalLimit.Glin
#check @Wu2008DoubleSieve.continuousOn_wuUpperCoefficient
#check @Wu2008DoubleSieve.continuousOn_wuLowerCoefficient
#print axioms Wu08OriginalFirstSteps.original_formula
#print axioms Wu08OriginalFirstSteps.upper_middle
#print axioms Wu08TerminalAlignment.first_exact
#print axioms Wu08TerminalAlignment.second_exact
#print axioms Wu08TerminalAlignment.first_actual_count

run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965" &&
        !s.contains '✝' then
      logInfo m!"{n}"

end WuPaper.RMapMFirst
