import RMapMSixthTypes

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve.wuLowerCoefficient" ||
        s.startsWith "MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965f_" ||
        s.startsWith "Wu2008DoubleSieve.truncatedSixthZeroDelta_" then
      logInfo m!"{n}: {ci.type}"
