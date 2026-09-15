import Lean
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackCross
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIndicator
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernel
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackParameters
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackCrossAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIndicatorAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIterated
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXi
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackParametersAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleContinuity
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBounds
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchange
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernelAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackIteratedAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXiAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalar
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleContinuityAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeighted
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBoundsAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchangeAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackAssemblyIntegral
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackLower
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalarAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedback
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackAssemblyIntegralAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackLowerAxiomCheck
import MathlibNt.Wu2008DoubleSieve.FirstFeedbackAxiomCheck

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`MathlibNt.Wu2008DoubleSieve.FirstFeedbackCross, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackIndicator, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernel, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackParameters, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangle, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernel, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackCrossAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackIndicatorAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackIterated, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXi, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackParametersAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleContinuity, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBounds, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchange, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedKernelAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackIteratedAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackKernelXiAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalar, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackTriangleContinuityAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeighted, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedBoundsAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedExchangeAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackAssemblyIntegral, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackLower, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackScalarAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackWeightedAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedback, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackAssemblyIntegralAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackLowerAxiomCheck, `MathlibNt.Wu2008DoubleSieve.FirstFeedbackAxiomCheck]
  for mod in modules do
    unless env.header.moduleNames.contains mod do
      throwError "missing target module {mod}"
    logInfo m!"ROUND16_MODULE|{mod}"
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
        logInfo m!"ROUND16_CONSTANT|{mod}|{kind}|{name}|unsafe={info.isUnsafe}"
