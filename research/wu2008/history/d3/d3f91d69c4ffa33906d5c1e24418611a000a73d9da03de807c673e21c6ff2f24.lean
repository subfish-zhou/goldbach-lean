import SrcSingleSevenWindows

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, c) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Wu2008DoubleSieve.secondFunctionalMother" &&
        !s.contains "_proof" && !s.contains ".eq_" &&
        !s.contains ".match_" && !s.contains "._" &&
        !(c.type.getUsedConstants.contains `Wu2008DoubleSieve.wuSourceBox) then
      logInfo m!"{n} : {c.type}"
