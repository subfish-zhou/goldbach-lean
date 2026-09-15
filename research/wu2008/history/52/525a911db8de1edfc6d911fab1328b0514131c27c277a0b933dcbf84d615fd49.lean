import Lean
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainIntegralsAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainFiniteAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainLimitsAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSourceAxiomCheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainIntegrals,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainIntegralsAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainFinite,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainFiniteAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainLimits,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainLimitsAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource,
    `MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSourceAxiomCheck]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "missing target module {mod}"
    logInfo m!"ROUND15_MODULE|{mod}"
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
        logInfo m!"ROUND15_CONSTANT|{mod}|{kind}|{name}|unsafe={info.isUnsafe}"
