import WE02JointCreditRoot
import Lean
open Lean Elab Command

elab "#e02_parent_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.E02JointCredit.difference_eq, `WuTarget.E02JointCredit.actual_jointCredit_lower,
      `WuTarget.E02JointCredit.paid_budget_gain, `WuTarget.E02JointCredit.ordinary_P2_with_amount] do
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

#e02_parent_cone

set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @WuTarget.W03.basis
#print axioms WuTarget.W03.basis
#check @WuTarget.W03.basis_nonneg
#print axioms WuTarget.W03.basis_nonneg
#check @WuTarget.W03.eval_expansion
#print axioms WuTarget.W03.eval_expansion
#check @WuTarget.W03.profile_expansion
#print axioms WuTarget.W03.profile_expansion
#check @WuTarget.W03.uniform_expansion
#print axioms WuTarget.W03.uniform_expansion
#check @WuTarget.W03.weight
#print axioms WuTarget.W03.weight
#check @WuTarget.W03.weight_nonneg
#print axioms WuTarget.W03.weight_nonneg
#check @WuTarget.W03.Gamma_expansion
#print axioms WuTarget.W03.Gamma_expansion
#check @WuTarget.W03.Gamma_eq_weights
#print axioms WuTarget.W03.Gamma_eq_weights
#check @WuTarget.W03.lower_weights_consumer
#print axioms WuTarget.W03.lower_weights_consumer
#check @WuTarget.W03.originalRow_left
#print axioms WuTarget.W03.originalRow_left
#check @WuTarget.W03.cell
#print axioms WuTarget.W03.cell
#check @WuTarget.W03.cell_unique
#print axioms WuTarget.W03.cell_unique
#check @WuTarget.W03.eval_basis
#print axioms WuTarget.W03.eval_basis
#check @WuTarget.W03.profile_basis
#print axioms WuTarget.W03.profile_basis
#check @WuTarget.W03.uniform_basis
#print axioms WuTarget.W03.uniform_basis
#check @WuTarget.W03.weight_integral
#print axioms WuTarget.W03.weight_integral
#check @WuTarget.W03.sumUpper
#print axioms WuTarget.W03.sumUpper
#check @WuTarget.W03.sumLower
#print axioms WuTarget.W03.sumLower
#check @WuTarget.W03.sliceLower
#print axioms WuTarget.W03.sliceLower
#check @WuTarget.W03.sliceUpper
#print axioms WuTarget.W03.sliceUpper
#check @WuTarget.W03.sliceLength
#print axioms WuTarget.W03.sliceLength
#check @WuTarget.W03.sum_bounds
#print axioms WuTarget.W03.sum_bounds
#check @WuTarget.W03.slice_domain
#print axioms WuTarget.W03.slice_domain
#check @WuTarget.W03.slice_cell
#print axioms WuTarget.W03.slice_cell
#check @WuTarget.W03.denominatorCap
#print axioms WuTarget.W03.denominatorCap
#check @WuTarget.W03.denominatorCap_pos
#print axioms WuTarget.W03.denominatorCap_pos
#check @WuTarget.W03.denominator_upper
#print axioms WuTarget.W03.denominator_upper
#check @WuTarget.W03.slice_kernel_lower
#print axioms WuTarget.W03.slice_kernel_lower
#check @WuTarget.W03.fibre_length_lower
#print axioms WuTarget.W03.fibre_length_lower
#check @WuTarget.W03.affine_integral
#print axioms WuTarget.W03.affine_integral
#check @WuTarget.W03.ramp_integral
#print axioms WuTarget.W03.ramp_integral
#check @WuTarget.W03.clipped_length_identity
#print axioms WuTarget.W03.clipped_length_identity
#check @WuTarget.W03.triangleArea
#print axioms WuTarget.W03.triangleArea
#check @WuTarget.W03.cellArea
#print axioms WuTarget.W03.cellArea
#check @WuTarget.W03.sliceLength_integral
#print axioms WuTarget.W03.sliceLength_integral
#check @WuTarget.W03.rationalWeight
#print axioms WuTarget.W03.rationalWeight
#check @WuTarget.W03.rationalWeight_le
#print axioms WuTarget.W03.rationalWeight_le
#check @WuTarget.W03.rationalWeight_pos
#print axioms WuTarget.W03.rationalWeight_pos
#check @WuTarget.W03.rational_weights_consumer
#print axioms WuTarget.W03.rational_weights_consumer
#check @WuTarget.W03.nodes_profile_lower
#print axioms WuTarget.W03.nodes_profile_lower
#check @WuTarget.W03.nodes_uniform_le_actual
#print axioms WuTarget.W03.nodes_uniform_le_actual
#check @WuTarget.W03.nodes_Gamma_payment
#print axioms WuTarget.W03.nodes_Gamma_payment
#check @WuTarget.W03.frozen
#print axioms WuTarget.W03.frozen
#check @WuTarget.W03.frozen_nonneg
#print axioms WuTarget.W03.frozen_nonneg
#check @WuTarget.W03.frozen_exact
#print axioms WuTarget.W03.frozen_exact
#check @WuTarget.W03.frozen_rational_lower
#print axioms WuTarget.W03.frozen_rational_lower
#check @WuTarget.W03.frozen_Hadm_payment
#print axioms WuTarget.W03.frozen_Hadm_payment
#check @WuTarget.W03.frozen_weighted_Hadm_payment
#print axioms WuTarget.W03.frozen_weighted_Hadm_payment
#check @WuTarget.W03.frozen_rational_Hadm_payment
#print axioms WuTarget.W03.frozen_rational_Hadm_payment
#check @WuTarget.W03.paidWeights
#print axioms WuTarget.W03.paidWeights
#check @WuTarget.W03.paidWeights_eq
#print axioms WuTarget.W03.paidWeights_eq
#check @WuTarget.W03.paidWeights_pos
#print axioms WuTarget.W03.paidWeights_pos
#check @WuTarget.W03.paidWeights_le
#print axioms WuTarget.W03.paidWeights_le
#check @WuTarget.W03.paid_weights_consumer
#print axioms WuTarget.W03.paid_weights_consumer
#check @WuTarget.W03.frozen_paid_lower
#print axioms WuTarget.W03.frozen_paid_lower
#check @WuTarget.W03.frozen_paid_Hadm_payment
#print axioms WuTarget.W03.frozen_paid_Hadm_payment
#check @WuTarget.W03.cell_sum_iff
#print axioms WuTarget.W03.cell_sum_iff
#check @WuTarget.W03.uniform_slice_support
#print axioms WuTarget.W03.uniform_slice_support
#check @WuTarget.W03.fibre_eq_uniform_integral
#print axioms WuTarget.W03.fibre_eq_uniform_integral
#check @WuTarget.W03.reciprocalKernel
#print axioms WuTarget.W03.reciprocalKernel
#check @WuTarget.W03.fibre_clipped
#print axioms WuTarget.W03.fibre_clipped
#check @WuTarget.W03.logPrimitive
#print axioms WuTarget.W03.logPrimitive
#check @WuTarget.W03.logPrimitive_derivative
#print axioms WuTarget.W03.logPrimitive_derivative
#check @WuTarget.W03.reciprocal_slice_integral
#print axioms WuTarget.W03.reciprocal_slice_integral
#check @WuTarget.W03.logSlice
#print axioms WuTarget.W03.logSlice
#check @WuTarget.W03.fibre_logSlice
#print axioms WuTarget.W03.fibre_logSlice
#check @WuTarget.W03.logSlice_integrable
#print axioms WuTarget.W03.logSlice_integrable
#check @WuTarget.W03.weight_one_dimensional
#print axioms WuTarget.W03.weight_one_dimensional
#check @WuTarget.E02JointCredit.difference
#print axioms WuTarget.E02JointCredit.difference
#check @WuTarget.E02JointCredit.addedMatrix
#print axioms WuTarget.E02JointCredit.addedMatrix
#check @WuTarget.E02JointCredit.increment_nonneg
#print axioms WuTarget.E02JointCredit.increment_nonneg
#check @WuTarget.E02JointCredit.augmented_le_joint
#print axioms WuTarget.E02JointCredit.augmented_le_joint
#check @WuTarget.E02JointCredit.addedMatrix_nonneg
#print axioms WuTarget.E02JointCredit.addedMatrix_nonneg
#check @WuTarget.E02JointCredit.frozen_subsolution
#print axioms WuTarget.E02JointCredit.frozen_subsolution
#check @WuTarget.E02JointCredit.previous_eq_update
#print axioms WuTarget.E02JointCredit.previous_eq_update
#check @WuTarget.E02JointCredit.seed_eq_old_add_increment
#print axioms WuTarget.E02JointCredit.seed_eq_old_add_increment
#check @WuTarget.E02JointCredit.increment_paid
#print axioms WuTarget.E02JointCredit.increment_paid
#check @WuTarget.E02JointCredit.enhanced_eq_update
#print axioms WuTarget.E02JointCredit.enhanced_eq_update
#check @WuTarget.E02JointCredit.increment_le_difference
#print axioms WuTarget.E02JointCredit.increment_le_difference
#check @WuTarget.E02JointCredit.difference_nonneg
#print axioms WuTarget.E02JointCredit.difference_nonneg
#check @WuTarget.E02JointCredit.difference_eq
#print axioms WuTarget.E02JointCredit.difference_eq
#check @WuTarget.E02JointCredit.difference_remainders_nonneg
#print axioms WuTarget.E02JointCredit.difference_remainders_nonneg
#check @WuTarget.E02JointCredit.transferredDifference
#print axioms WuTarget.E02JointCredit.transferredDifference
#check @WuTarget.E02JointCredit.transferredDifference_nonneg
#print axioms WuTarget.E02JointCredit.transferredDifference_nonneg
#check @WuTarget.E02JointCredit.transferredDifference_eq
#print axioms WuTarget.E02JointCredit.transferredDifference_eq
#check @WuTarget.E02JointCredit.jointCredit_eq_gamma
#print axioms WuTarget.E02JointCredit.jointCredit_eq_gamma
#check @WuTarget.E02JointCredit.jointCredit_eq_weights
#print axioms WuTarget.E02JointCredit.jointCredit_eq_weights
#check @WuTarget.E02JointCredit.paid_difference_lower
#print axioms WuTarget.E02JointCredit.paid_difference_lower
#check @WuTarget.E02JointCredit.rational_difference_lower
#print axioms WuTarget.E02JointCredit.rational_difference_lower
#check @WuTarget.E02JointCredit.first_transfer_paid
#print axioms WuTarget.E02JointCredit.first_transfer_paid
#check @WuTarget.E02JointCredit.first_difference_paid
#print axioms WuTarget.E02JointCredit.first_difference_paid
#check @WuTarget.E02JointCredit.amount
#print axioms WuTarget.E02JointCredit.amount
#check @WuTarget.E02JointCredit.amount_eq
#print axioms WuTarget.E02JointCredit.amount_eq
#check @WuTarget.E02JointCredit.amount_le_jointCredit
#print axioms WuTarget.E02JointCredit.amount_le_jointCredit
#check @WuTarget.E02JointCredit.amount_gt_simple
#print axioms WuTarget.E02JointCredit.amount_gt_simple
#check @WuTarget.E02JointCredit.jointCredit_pos
#print axioms WuTarget.E02JointCredit.jointCredit_pos
#check @WuTarget.E02JointCredit.actual_jointCredit_lower
#print axioms WuTarget.E02JointCredit.actual_jointCredit_lower
#check @WuTarget.E02JointCredit.actual_jointCredit_gt
#print axioms WuTarget.E02JointCredit.actual_jointCredit_gt
#check @WuTarget.E02JointCredit.actual_lowGain_difference_lower
#print axioms WuTarget.E02JointCredit.actual_lowGain_difference_lower
#check @WuTarget.E02JointCredit.actual_coefficient_gain
#print axioms WuTarget.E02JointCredit.actual_coefficient_gain
#check @WuTarget.E02JointCredit.paid_budget_gain
#print axioms WuTarget.E02JointCredit.paid_budget_gain
#check @WuTarget.E02JointCredit.remaining_budget_gain
#print axioms WuTarget.E02JointCredit.remaining_budget_gain
#check @WuTarget.E02JointCredit.net_amount_identity
#print axioms WuTarget.E02JointCredit.net_amount_identity
#check @WuTarget.E02JointCredit.net_remainder_nonneg
#print axioms WuTarget.E02JointCredit.net_remainder_nonneg
#check @WuTarget.E02JointCredit.ordinary_P2_with_amount
#print axioms WuTarget.E02JointCredit.ordinary_P2_with_amount
