import RMapMSixthClassical

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if ((s.splitOn "jr1965").length > 1 && (s.splitOn "ontinuous").length > 1) ||
        s.startsWith "intervalIntegral.norm_integral_le_of_norm_le_const" ||
        s.startsWith "Wu2008DoubleSieve.gamma5Gain_moving_integral" then
      logInfo m!"{n}: {ci.type}"
