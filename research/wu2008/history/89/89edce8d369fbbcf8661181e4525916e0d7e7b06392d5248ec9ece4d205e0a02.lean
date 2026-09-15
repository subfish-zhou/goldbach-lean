import SrcSixthGainConsumer
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "Wu2008DoubleSieve.wuImprovementLimit" then
      logInfo m!"{name} : {info.type}"
