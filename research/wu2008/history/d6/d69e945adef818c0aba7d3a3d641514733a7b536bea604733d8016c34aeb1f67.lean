import Wu08TerminalAlignment

open Lean Elab Command
namespace WuPaper.RMapMFirst
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open Wu2008DoubleSieve

#check @jr1965F_initial
#check @jr1965f_initial
#check @jr1965F_normalized_initial
#check @jr1965f_normalized_firstInterval
#check @jr1965f_nonneg
#check @jr1965F_pos
#check @intervalIntegral.integral_comp_mul_left
#check @intervalIntegral.integral_comp_add_left
#check @intervalIntegral.integral_comp_sub_left
#check @IntervalIntegrable.congr
#check @intervalIntegral.integral_congr
#check @HasDerivAt.congr_of_eventuallyEq

run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if (s.contains "jr1965" && (s.contains "eriv" || s.contains "ontinuous" ||
        s.contains "normalized")) && !(s.contains "_proof") && !(s.contains "_simp") then
      logInfo m!"{n} : {ci.type}"

end WuPaper.RMapMFirst
