import Lean
import MathlibNt.Wu2008DoubleSieve.FiniteWeights
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Wu2008DoubleSieve.inst" then
      logInfo m!"{name}"
