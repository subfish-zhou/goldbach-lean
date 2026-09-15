import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackRegularity
import Lean.Util.FoldConsts

/-!
# Complete stored-member types, dependencies, and logical axiom cones

No prefix or current-owner filter is applied to moduleData.constNames.
-/

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.maxSteps 1000000

open Lean Elab Term

run_elab do
  let env ← getEnv
  let modules := #[
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackKernel,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackSlices,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackBounds,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackLoss,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackTransport,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackMain,
    `MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackRegularity]
  let mut total := 0
  for modName in modules do
    let some idx := env.getModuleIdx? modName
      | throwError "Missing module: {modName}"
    let names := env.header.moduleData[idx.toNat]!.constNames
    logInfo (Json.mkObj [
      ("module", toJson modName.toString),
      ("constNames_count", toJson names.size)]).compress
    for name in names do
      let some ci := env.checked.get.find? name
        | throwError "Missing module member: {name}"
      if let .axiomInfo _ := ci then
        throwError "New axiom declaration: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Nonstandard axiom: {name}: {ax}"
      let type ← Meta.ppExpr ci.type
      let mut deps : Array String := #[]
      for dep in ci.getUsedConstantsAsSet do
        deps := deps.push dep.toString
      logInfo (Json.mkObj [
        ("module", toJson modName.toString),
        ("name", toJson name.toString),
        ("type", toJson type.pretty),
        ("direct_dependencies", toJson deps),
        ("axioms", toJson (axioms.map Name.toString))]).compress
      total := total + 1
  let own ← mkModuleData env
  unless own.constNames.isEmpty do
    throwError "Command-only audit unexpectedly introduced declarations: {own.constNames}"
  logInfo (Json.mkObj [
    ("module", toJson env.mainModule.toString),
    ("constNames_count", toJson own.constNames.size)]).compress
  logInfo (Json.mkObj [("complete_module_member_total", toJson total)]).compress

set_option pp.explicit false
set_option pp.proofs false

open Wu2008DoubleSieve

#print gamma5FeedbackFullKernel
#print gamma5FeedbackLegalKernel
#print gamma5FeedbackLossKernel
#print gamma5FeedbackFullGain
#print gamma5FeedbackB
#print gamma5FeedbackA
#print gamma5FeedbackR
#print gamma5FeedbackLegalMiddle
#print gamma5FeedbackP
#print gamma5FeedbackW
#print gamma5GainIntegral
#print gamma5ClassicalLabels
#print gamma5ClassicalCount
#print gamma5ClassicalMainMass
#print gamma5MassC5
#print boxTheta
#print AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral

#check @gamma5Feedback_breakpoints
#check @gamma5Feedback_joins
#check @gamma5Feedback_full_slice
#check @gamma5Feedback_legal_slice
#check @gamma5Feedback_kernel_identity
#check @gamma5Feedback_kernels_nonnegative
#check @gamma5Feedback_full_legal_bounds
#check @gamma5Feedback_loss_bounds
#check @gamma5Feedback_kernel_support
#check @gamma5Feedback_full_integrable
#check @gamma5Feedback_legal_integrable
#check @gamma5Feedback_loss_integrable
#check @gamma5Feedback_source_integrable
#check @gamma5Feedback_weighted_integrable
#check @gamma5Feedback_inner_substitution
#check @gamma5Feedback_transport
#check @gamma5Feedback_full_inner_integrable
#check @gamma5Feedback_full_outer_integrable
#check @gamma5Feedback_legal_gain_eq
#check @gamma5Feedback_full_gain_eq
#check @gamma5Feedback_loss_gain_eq
#check @gamma5Feedback_full_count_upper
#check @firstFeedbackWeightedKernel_integral
#check @gamma5Gain_full_count_upper

#print axioms gamma5Feedback_full_count_upper
#print axioms gamma5Feedback_legal_gain_eq
#print axioms gamma5Feedback_full_gain_eq
#print axioms gamma5Feedback_loss_gain_eq
#print axioms gamma5Feedback_kernel_identity
