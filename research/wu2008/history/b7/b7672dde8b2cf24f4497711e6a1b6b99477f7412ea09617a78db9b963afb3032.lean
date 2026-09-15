import Lean
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeighted
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernelAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBoundsAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchangeAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedAxiomCheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBounds,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchange,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeighted,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernelAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBoundsAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchangeAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedAxiomCheck]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "missing target module {mod}"
    logInfo m!"ROUND16_WEIGHTED_MODULE|{mod}"
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if modules.contains mod then
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "def"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        logInfo m!"ROUND16_WEIGHTED_CONSTANT|{mod}|{kind}|{name}|unsafe={info.isUnsafe}"
