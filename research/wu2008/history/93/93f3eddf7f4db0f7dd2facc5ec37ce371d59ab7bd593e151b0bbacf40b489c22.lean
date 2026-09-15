import WE07FifthSourceRoot
import Lean
open Lean Elab Command

elab "#we07sourceparentaudit_cone" : command => do
  let env := (← getEnv).setExporting false
  for root in #[`WuTarget.Wu08FifthSource.source_formula_to_fifthMain, `WuTarget.Wu08FifthSource.source_three_integrals, `WuTarget.Wu08FifthSource.recurrence_one_dimensional, `WuTarget.Wu08FifthSource.coefficient_error_transport] do
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

#we07sourceparentaudit_cone

set_option pp.proofs true
set_option pp.deepTerms true
#check @WuTarget.Wu08FifthSource.paperKernel
#print axioms WuTarget.Wu08FifthSource.paperKernel
#check @WuTarget.Wu08FifthSource.paperClassical
#print axioms WuTarget.Wu08FifthSource.paperClassical
#check @WuTarget.Wu08FifthSource.parameters_exact
#print axioms WuTarget.Wu08FifthSource.parameters_exact
#check @WuTarget.Wu08FifthSource.coefficient_initial
#print axioms WuTarget.Wu08FifthSource.coefficient_initial
#check @WuTarget.Wu08FifthSource.coefficient_recurrence
#print axioms WuTarget.Wu08FifthSource.coefficient_recurrence
#check @WuTarget.Wu08FifthSource.parameter_range
#print axioms WuTarget.Wu08FifthSource.parameter_range
#check @WuTarget.Wu08FifthSource.triangle_outer_first
#print axioms WuTarget.Wu08FifthSource.triangle_outer_first
#check @WuTarget.Wu08FifthSource.paper_inner_substitution
#print axioms WuTarget.Wu08FifthSource.paper_inner_substitution
#check @WuTarget.Wu08FifthSource.paper_classical_eq_fifthMain
#print axioms WuTarget.Wu08FifthSource.paper_classical_eq_fifthMain
#check @WuTarget.Wu08FifthSource.sumShear
#print axioms WuTarget.Wu08FifthSource.sumShear
#check @WuTarget.Wu08FifthSource.sumKernel
#print axioms WuTarget.Wu08FifthSource.sumKernel
#check @WuTarget.Wu08FifthSource.sliceLower
#print axioms WuTarget.Wu08FifthSource.sliceLower
#check @WuTarget.Wu08FifthSource.reducedKernel
#print axioms WuTarget.Wu08FifthSource.reducedKernel
#check @WuTarget.Wu08FifthSource.sum_shear_preserving
#print axioms WuTarget.Wu08FifthSource.sum_shear_preserving
#check @WuTarget.Wu08FifthSource.sum_kernel_integrable
#print axioms WuTarget.Wu08FifthSource.sum_kernel_integrable
#check @WuTarget.Wu08FifthSource.sum_kernel_integral
#print axioms WuTarget.Wu08FifthSource.sum_kernel_integral
#check @WuTarget.Wu08FifthSource.slice_geometry
#print axioms WuTarget.Wu08FifthSource.slice_geometry
#check @WuTarget.Wu08FifthSource.sum_region_iff
#print axioms WuTarget.Wu08FifthSource.sum_region_iff
#check @WuTarget.Wu08FifthSource.pair_reciprocal_ftc
#print axioms WuTarget.Wu08FifthSource.pair_reciprocal_ftc
#check @WuTarget.Wu08FifthSource.sum_inner_integral
#print axioms WuTarget.Wu08FifthSource.sum_inner_integral
#check @WuTarget.Wu08FifthSource.fifth_main_one_dimensional
#print axioms WuTarget.Wu08FifthSource.fifth_main_one_dimensional
#check @WuTarget.Wu08FifthSource.paperA
#print axioms WuTarget.Wu08FifthSource.paperA
#check @WuTarget.Wu08FifthSource.geometricSplit
#print axioms WuTarget.Wu08FifthSource.geometricSplit
#check @WuTarget.Wu08FifthSource.lowerBranch
#print axioms WuTarget.Wu08FifthSource.lowerBranch
#check @WuTarget.Wu08FifthSource.upperBranch
#print axioms WuTarget.Wu08FifthSource.upperBranch
#check @WuTarget.Wu08FifthSource.scalarReduced
#print axioms WuTarget.Wu08FifthSource.scalarReduced
#check @WuTarget.Wu08FifthSource.paper_a_eq
#print axioms WuTarget.Wu08FifthSource.paper_a_eq
#check @WuTarget.Wu08FifthSource.paper_kernel_literal
#print axioms WuTarget.Wu08FifthSource.paper_kernel_literal
#check @WuTarget.Wu08FifthSource.paper_a_original_integral
#print axioms WuTarget.Wu08FifthSource.paper_a_original_integral
#check @WuTarget.Wu08FifthSource.fixed_breakpoints
#print axioms WuTarget.Wu08FifthSource.fixed_breakpoints
#check @WuTarget.Wu08FifthSource.scalar_reduced_literal
#print axioms WuTarget.Wu08FifthSource.scalar_reduced_literal
#check @WuTarget.Wu08FifthSource.scalar_parameter_transport
#print axioms WuTarget.Wu08FifthSource.scalar_parameter_transport
#check @WuTarget.Wu08FifthSource.source_finite_cover
#print axioms WuTarget.Wu08FifthSource.source_finite_cover
#check @WuTarget.Wu08FifthSource.scalar_geometry
#print axioms WuTarget.Wu08FifthSource.scalar_geometry
#check @WuTarget.Wu08FifthSource.scalar_reduced_continuous
#print axioms WuTarget.Wu08FifthSource.scalar_reduced_continuous
#check @WuTarget.Wu08FifthSource.scalar_interval_integrable
#print axioms WuTarget.Wu08FifthSource.scalar_interval_integrable
#check @WuTarget.Wu08FifthSource.upper_branch_literal
#print axioms WuTarget.Wu08FifthSource.upper_branch_literal
#check @WuTarget.Wu08FifthSource.lower_branch_literal
#print axioms WuTarget.Wu08FifthSource.lower_branch_literal
#check @WuTarget.Wu08FifthSource.source_three_integrals
#print axioms WuTarget.Wu08FifthSource.source_three_integrals
#check @WuTarget.Wu08FifthSource.initial_branch_formula
#print axioms WuTarget.Wu08FifthSource.initial_branch_formula
#check @WuTarget.Wu08FifthSource.recurrence_lower_formula
#print axioms WuTarget.Wu08FifthSource.recurrence_lower_formula
#check @WuTarget.Wu08FifthSource.recurrence_upper_formula
#print axioms WuTarget.Wu08FifthSource.recurrence_upper_formula
#check @WuTarget.Wu08FifthSource.paper_classical_actual_count
#print axioms WuTarget.Wu08FifthSource.paper_classical_actual_count
#check @WuTarget.Wu08FifthSource.recurrenceIntegrand
#print axioms WuTarget.Wu08FifthSource.recurrenceIntegrand
#check @WuTarget.Wu08FifthSource.B_derivative
#print axioms WuTarget.Wu08FifthSource.B_derivative
#check @WuTarget.Wu08FifthSource.recurrence_one_dimensional
#print axioms WuTarget.Wu08FifthSource.recurrence_one_dimensional
#check @WuTarget.Wu08FifthSource.coefficient_single_recurrence
#print axioms WuTarget.Wu08FifthSource.coefficient_single_recurrence
#check @WuTarget.Wu08FifthSource.recurrence_integrand_nonneg
#print axioms WuTarget.Wu08FifthSource.recurrence_integrand_nonneg
#check @WuTarget.Wu08FifthSource.reducedWeight
#print axioms WuTarget.Wu08FifthSource.reducedWeight
#check @WuTarget.Wu08FifthSource.reduced_weight_bounds
#print axioms WuTarget.Wu08FifthSource.reduced_weight_bounds
#check @WuTarget.Wu08FifthSource.reduced_weight_continuous
#print axioms WuTarget.Wu08FifthSource.reduced_weight_continuous
#check @WuTarget.Wu08FifthSource.scalar_weight_identity
#print axioms WuTarget.Wu08FifthSource.scalar_weight_identity
#check @WuTarget.Wu08FifthSource.coefficient_error_transport
#print axioms WuTarget.Wu08FifthSource.coefficient_error_transport
#check @WuTarget.Wu08FifthSource.source_formula_to_fifthMain
#print axioms WuTarget.Wu08FifthSource.source_formula_to_fifthMain
#check @WuTarget.Wu08FifthSource.source_a_formula_to_fifthMain
#print axioms WuTarget.Wu08FifthSource.source_a_formula_to_fifthMain
