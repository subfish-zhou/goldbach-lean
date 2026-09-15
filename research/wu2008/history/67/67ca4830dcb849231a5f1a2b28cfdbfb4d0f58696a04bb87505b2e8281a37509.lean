import Lean
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleAxiomCheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleAxiomCheck]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for module in modules do
    unless env.header.moduleNames.contains module do
      throwError "Missing module {module}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[idx.toNat]!
      if modules.contains module then
        unless info.isTheorem do
          throwError "Unexpected non-theorem declaration {name}"
        if info.isUnsafe then
          throwError "Unsafe declaration {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
        logInfo m!"TRIANGLE_CONSTANT|{module}|{name}|{axioms}"
        count := count + 1
  logInfo m!"TRIANGLE_CONSTANT_COUNT|{count}"
