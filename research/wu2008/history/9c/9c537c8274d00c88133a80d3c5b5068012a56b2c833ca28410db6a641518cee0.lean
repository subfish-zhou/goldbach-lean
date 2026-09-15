import WE04AcceptedBudget
import W01ContinuousRoot
import Lean
open Lean Elab Command

elab "#e04_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E04Continuous.surplus_linear, `WuTarget.E04Continuous.enhanced_surplus_rational,
      `WuTarget.EveningContinuousAccepted.ordinary_P2, `WuTarget.EveningContinuousAccepted.refined_target] do
    let mut todo := #[root]
    let mut seen : Std.HashSet Name := {}
    let mut missing : Array Name := #[]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      if !seen.contains n then
        seen := seen.insert n
        if seen.size == 200000 then logInfo "expanded consumer exceeds old diagnostic-size cutoff; continuing full finite visited-set traversal"
        match env.checked.get.find? n with
        | none => missing := missing.push n
        | some ci =>
          todo := todo ++ ci.type.getUsedConstants
          match ci with
          | .defnInfo v => todo := todo ++ v.value.getUsedConstants
          | .thmInfo v => todo := todo ++ v.value.getUsedConstants
          | .opaqueInfo v => todo := todo ++ v.value.getUsedConstants
          | .inductInfo v => todo := todo ++ v.ctors.toArray
          | _ => pure ()
    let names := seen.toArray.map Name.toString
    let watched := names.filter fun n =>
      n.endsWith ".Cinf" || n.endsWith ".Ainf" || n.endsWith ".originalH" ||
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".C_tendsto" ||
      n.endsWith ".Ainf_le_supersolution" || n.endsWith ".subsolution_le_Ainf" ||
      n.endsWith ".actual_comparison_same_delta"
    let forbidden := names.filter fun n =>
      n.endsWith ".Cinf_Hadm_payment" || n.endsWith ".Ainf_le_supersolution" ||
      n.endsWith ".subsolution_le_Ainf" || n.endsWith ".actual_comparison_same_delta"
    let out ← IO.getStdout
    out.putStrLn <| (Json.mkObj [("root", toJson root.toString),
      ("visited", toJson seen.size), ("missing", toJson (missing.map Name.toString)),
      ("watched", toJson watched), ("forbidden", toJson forbidden)]).compress
    out.flush
    unless missing.isEmpty && forbidden.isEmpty do throwError "method audit failed"

#e04_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @WuTarget.W01Continuous.upperProfile
#print axioms WuTarget.W01Continuous.upperProfile
#check @WuTarget.W01Continuous.hContinuous
#print axioms WuTarget.W01Continuous.hContinuous
#check @WuTarget.W01Continuous.rNode_strictMono
#print axioms WuTarget.W01Continuous.rNode_strictMono
#check @WuTarget.W01Continuous.extendedNode_mono
#print axioms WuTarget.W01Continuous.extendedNode_mono
#check @WuTarget.W01Continuous.upper_cells_unique
#print axioms WuTarget.W01Continuous.upper_cells_unique
#check @WuTarget.W01Continuous.upperProfile_initial
#print axioms WuTarget.W01Continuous.upperProfile_initial
#check @WuTarget.W01Continuous.upperProfile_cell
#print axioms WuTarget.W01Continuous.upperProfile_cell
#check @WuTarget.W01Continuous.upperProfile_nonneg
#print axioms WuTarget.W01Continuous.upperProfile_nonneg
#check @WuTarget.W01Continuous.upperProfile_zero_outside
#print axioms WuTarget.W01Continuous.upperProfile_zero_outside
#check @WuTarget.W01Continuous.upperProfile_le_actual
#print axioms WuTarget.W01Continuous.upperProfile_le_actual
#check @WuTarget.W01Continuous.upperProfile_div_integrable
#print axioms WuTarget.W01Continuous.upperProfile_div_integrable
#check @WuTarget.W01Continuous.upperProfile_div_nonneg
#print axioms WuTarget.W01Continuous.upperProfile_div_nonneg
#check @WuTarget.W01Continuous.hContinuous_continuous
#print axioms WuTarget.W01Continuous.hContinuous_continuous
#check @WuTarget.W01Continuous.hContinuous_antitone
#print axioms WuTarget.W01Continuous.hContinuous_antitone
#check @WuTarget.W01Continuous.hContinuous_nonneg
#print axioms WuTarget.W01Continuous.hContinuous_nonneg
#check @WuTarget.W01Continuous.hContinuous_le_actual
#print axioms WuTarget.W01Continuous.hContinuous_le_actual
#check @WuTarget.W01Continuous.upperProfile_cell_integral
#print axioms WuTarget.W01Continuous.upperProfile_cell_integral
#check @WuTarget.W01Continuous.upperProfile_initial_integral
#print axioms WuTarget.W01Continuous.upperProfile_initial_integral
#check @WuTarget.W01Continuous.hContinuous_node_nat
#print axioms WuTarget.W01Continuous.hContinuous_node_nat
#check @WuTarget.W01Continuous.hContinuous_node
#print axioms WuTarget.W01Continuous.hContinuous_node
#check @WuTarget.W01Continuous.old_profile_le_continuous
#print axioms WuTarget.W01Continuous.old_profile_le_continuous
#check @WuTarget.W01Continuous.continuousUniform
#print axioms WuTarget.W01Continuous.continuousUniform
#check @WuTarget.W01Continuous.continuousGamma
#print axioms WuTarget.W01Continuous.continuousGamma
#check @WuTarget.W01Continuous.continuousGain
#print axioms WuTarget.W01Continuous.continuousGain
#check @WuTarget.W01Continuous.continuousBound
#print axioms WuTarget.W01Continuous.continuousBound
#check @WuTarget.W01Continuous.continuousBound_nonneg
#print axioms WuTarget.W01Continuous.continuousBound_nonneg
#check @WuTarget.W01Continuous.u_bounds
#print axioms WuTarget.W01Continuous.u_bounds
#check @WuTarget.W01Continuous.continuous_kernel_bounds
#print axioms WuTarget.W01Continuous.continuous_kernel_bounds
#check @WuTarget.W01Continuous.measurable_continuous_kernel
#print axioms WuTarget.W01Continuous.measurable_continuous_kernel
#check @WuTarget.W01Continuous.continuousUniform_integrable
#print axioms WuTarget.W01Continuous.continuousUniform_integrable
#check @WuTarget.W01Continuous.continuousUniform_nonneg
#print axioms WuTarget.W01Continuous.continuousUniform_nonneg
#check @WuTarget.W01Continuous.continuousGain_nonneg
#print axioms WuTarget.W01Continuous.continuousGain_nonneg
#check @WuTarget.W01Continuous.lowGain_le_continuousGain
#print axioms WuTarget.W01Continuous.lowGain_le_continuousGain
#check @WuTarget.W01Continuous.continuousUniform_le_actual
#print axioms WuTarget.W01Continuous.continuousUniform_le_actual
#check @WuTarget.W01Continuous.continuousGamma_payment
#print axioms WuTarget.W01Continuous.continuousGamma_payment
#check @WuTarget.W01Continuous.continuousFibre
#print axioms WuTarget.W01Continuous.continuousFibre
#check @WuTarget.W01Continuous.continuousMeasurableFibre
#print axioms WuTarget.W01Continuous.continuousMeasurableFibre
#check @WuTarget.W01Continuous.continuousStrip
#print axioms WuTarget.W01Continuous.continuousStrip
#check @WuTarget.W01Continuous.continuousLoss
#print axioms WuTarget.W01Continuous.continuousLoss
#check @WuTarget.W01Continuous.continuousLoss_nonneg
#print axioms WuTarget.W01Continuous.continuousLoss_nonneg
#check @WuTarget.W01Continuous.continuous_segment_integrable
#print axioms WuTarget.W01Continuous.continuous_segment_integrable
#check @WuTarget.W01Continuous.continuous_inner_integrable
#print axioms WuTarget.W01Continuous.continuous_inner_integrable
#check @WuTarget.W01Continuous.continuous_strip_integrable
#print axioms WuTarget.W01Continuous.continuous_strip_integrable
#check @WuTarget.W01Continuous.continuous_fibre_difference
#print axioms WuTarget.W01Continuous.continuous_fibre_difference
#check @WuTarget.W01Continuous.continuous_strip_bounds
#print axioms WuTarget.W01Continuous.continuous_strip_bounds
#check @WuTarget.W01Continuous.continuous_measurable_fibre
#print axioms WuTarget.W01Continuous.continuous_measurable_fibre
#check @WuTarget.W01Continuous.continuous_measurableFibre_eq
#print axioms WuTarget.W01Continuous.continuous_measurableFibre_eq
#check @WuTarget.W01Continuous.continuous_fibre_bounds
#print axioms WuTarget.W01Continuous.continuous_fibre_bounds
#check @WuTarget.W01Continuous.continuous_outer_integrable
#print axioms WuTarget.W01Continuous.continuous_outer_integrable
#check @WuTarget.W01Continuous.continuous_outer_strip_integrable
#print axioms WuTarget.W01Continuous.continuous_outer_strip_integrable
#check @WuTarget.W01Continuous.continuousGamma_eq_fibres
#print axioms WuTarget.W01Continuous.continuousGamma_eq_fibres
#check @WuTarget.W01Continuous.continuousGamma_difference
#print axioms WuTarget.W01Continuous.continuousGamma_difference
#check @WuTarget.W01Continuous.continuousGain_loss
#print axioms WuTarget.W01Continuous.continuousGain_loss
#check @WuTarget.W01Continuous.continuousGain_Hadm_payment
#print axioms WuTarget.W01Continuous.continuousGain_Hadm_payment
#check @WuTarget.W01Continuous.continuousCoefficient
#print axioms WuTarget.W01Continuous.continuousCoefficient
#check @WuTarget.W01Continuous.continuousCoefficient_eq
#print axioms WuTarget.W01Continuous.continuousCoefficient_eq
#check @WuTarget.W01Continuous.old_coefficient_le_continuous
#print axioms WuTarget.W01Continuous.old_coefficient_le_continuous
#check @WuTarget.W01Continuous.continuous_B_normalization
#print axioms WuTarget.W01Continuous.continuous_B_normalization
#check @WuTarget.W01Continuous.continuous_mixed_normalization
#print axioms WuTarget.W01Continuous.continuous_mixed_normalization
#check @WuTarget.W01Continuous.continuous_coefficient_cap
#print axioms WuTarget.W01Continuous.continuous_coefficient_cap
#check @WuTarget.W01Continuous.continuous_ordinary_P2
#print axioms WuTarget.W01Continuous.continuous_ordinary_P2
#check @WuTarget.W01Continuous.v8_continuousGain_payment
#print axioms WuTarget.W01Continuous.v8_continuousGain_payment
#check @WuTarget.W01Continuous.v8_continuous_ordinary_P2
#print axioms WuTarget.W01Continuous.v8_continuous_ordinary_P2
#check @WuTarget.W01Continuous.v8_old_gain_le_continuous
#print axioms WuTarget.W01Continuous.v8_old_gain_le_continuous
#check @WuTarget.W01Continuous.v8_old_coefficient_le_continuous
#print axioms WuTarget.W01Continuous.v8_old_coefficient_le_continuous
#check @WuTarget.E04Continuous.first_profile
#print axioms WuTarget.E04Continuous.first_profile
#check @WuTarget.E04Continuous.first_cell_surplus
#print axioms WuTarget.E04Continuous.first_cell_surplus
#check @WuTarget.E04Continuous.rectangle
#print axioms WuTarget.E04Continuous.rectangle
#check @WuTarget.E04Continuous.rectangle_geometry
#print axioms WuTarget.E04Continuous.rectangle_geometry
#check @WuTarget.E04Continuous.rectangle_kernel_surplus
#print axioms WuTarget.E04Continuous.rectangle_kernel_surplus
#check @WuTarget.E04Continuous.surplusDensity
#print axioms WuTarget.E04Continuous.surplusDensity
#check @WuTarget.E04Continuous.surplusDensity_integrable
#print axioms WuTarget.E04Continuous.surplusDensity_integrable
#check @WuTarget.E04Continuous.surplusDensity_nonneg
#print axioms WuTarget.E04Continuous.surplusDensity_nonneg
#check @WuTarget.E04Continuous.net_integral
#print axioms WuTarget.E04Continuous.net_integral
#check @WuTarget.E04Continuous.rectangle_measurable
#print axioms WuTarget.E04Continuous.rectangle_measurable
#check @WuTarget.E04Continuous.rectangle_volume
#print axioms WuTarget.E04Continuous.rectangle_volume
#check @WuTarget.E04Continuous.surplus_linear
#print axioms WuTarget.E04Continuous.surplus_linear
#check @WuTarget.E04Continuous.certifiedAmount
#print axioms WuTarget.E04Continuous.certifiedAmount
#check @WuTarget.E04Continuous.netCredit
#print axioms WuTarget.E04Continuous.netCredit
#check @WuTarget.E04Continuous.replacementCoefficient
#print axioms WuTarget.E04Continuous.replacementCoefficient
#check @WuTarget.E04Continuous.replacementPaidCoefficient
#print axioms WuTarget.E04Continuous.replacementPaidCoefficient
#check @WuTarget.E04Continuous.enhanced_zero_lower
#print axioms WuTarget.E04Continuous.enhanced_zero_lower
#check @WuTarget.E04Continuous.enhanced_surplus_linear
#print axioms WuTarget.E04Continuous.enhanced_surplus_linear
#check @WuTarget.E04Continuous.enhanced_surplus_rational
#print axioms WuTarget.E04Continuous.enhanced_surplus_rational
#check @WuTarget.E04Continuous.certifiedAmount_pos
#print axioms WuTarget.E04Continuous.certifiedAmount_pos
#check @WuTarget.E04Continuous.netCredit_gt_display
#print axioms WuTarget.E04Continuous.netCredit_gt_display
#check @WuTarget.E04Continuous.certifiedAmount_le_netCredit
#print axioms WuTarget.E04Continuous.certifiedAmount_le_netCredit
#check @WuTarget.E04Continuous.netCredit_pos
#print axioms WuTarget.E04Continuous.netCredit_pos
#check @WuTarget.E04Continuous.replacement_identity
#print axioms WuTarget.E04Continuous.replacement_identity
#check @WuTarget.E04Continuous.netCredit_identity
#print axioms WuTarget.E04Continuous.netCredit_identity
#check @WuTarget.E04Continuous.replacement_gain_strict
#print axioms WuTarget.E04Continuous.replacement_gain_strict
#check @WuTarget.E04Continuous.replacementPaid_net_identity
#print axioms WuTarget.E04Continuous.replacementPaid_net_identity
#check @WuTarget.E04Continuous.replacementPaid_lt_actual
#print axioms WuTarget.E04Continuous.replacementPaid_lt_actual
#check @WuTarget.E04Continuous.enhanced_continuous_Hadm
#print axioms WuTarget.E04Continuous.enhanced_continuous_Hadm
#check @WuTarget.E04Continuous.enhanced_continuous_ordinary_P2
#print axioms WuTarget.E04Continuous.enhanced_continuous_ordinary_P2
#check @WuTarget.E04Continuous.replacement_paid_ordinary_P2
#print axioms WuTarget.E04Continuous.replacement_paid_ordinary_P2
#check @WuTarget.E04Continuous.replacement_threshold_iff
#print axioms WuTarget.E04Continuous.replacement_threshold_iff
#check @WuTarget.E04Continuous.replacement_refined_target
#print axioms WuTarget.E04Continuous.replacement_refined_target
#check @WuTarget.EveningContinuousAccepted.tableGain
#print axioms WuTarget.EveningContinuousAccepted.tableGain
#check @WuTarget.EveningContinuousAccepted.otherRemaining
#print axioms WuTarget.EveningContinuousAccepted.otherRemaining
#check @WuTarget.EveningContinuousAccepted.certifiedCredits
#print axioms WuTarget.EveningContinuousAccepted.certifiedCredits
#check @WuTarget.EveningContinuousAccepted.scalar_paid_le
#print axioms WuTarget.EveningContinuousAccepted.scalar_paid_le
#check @WuTarget.EveningContinuousAccepted.ordinary_P2
#print axioms WuTarget.EveningContinuousAccepted.ordinary_P2
#check @WuTarget.EveningContinuousAccepted.refined_target
#print axioms WuTarget.EveningContinuousAccepted.refined_target
