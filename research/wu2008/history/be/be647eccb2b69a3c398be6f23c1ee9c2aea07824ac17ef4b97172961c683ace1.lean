import Lean
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXiAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelAxiomCheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernel,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelAxiomCheck,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXi,
    `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXiAxiomCheck]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "missing target module {mod}"
    logInfo m!"KERNEL_MODULE|{mod}"
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
        logInfo m!"KERNEL_CONSTANT|{mod}|{kind}|{name}|unsafe={info.isUnsafe}"
