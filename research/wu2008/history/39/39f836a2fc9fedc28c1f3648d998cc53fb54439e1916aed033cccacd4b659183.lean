import WSourceCoreInspect4
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for n in [`Wu2008DoubleSieve.wuImprovementLimit,
      `Wu2008DoubleSieve.wuAdmissibleImprovements,
      `Wu2008DoubleSieve.SecondFunctionalParameters,
      `Wu2008DoubleSieve.sourceSieveCarrier] do
    match env.getModuleIdxFor? n with
    | some i => logInfo m!"{n}: {env.header.moduleNames[i]!}"
    | none => logInfo m!"{n}: current module or missing owner"
