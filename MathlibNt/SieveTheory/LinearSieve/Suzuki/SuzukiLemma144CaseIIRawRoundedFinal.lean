import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedTransportRefactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIErrorTransportUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIEndpointGap
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBracketGapQuantitative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ExplicitRemaindersSourceOrder

import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- The source parity indices coincide with the actual recurrence carrier. -/
theorem sourceParityIndices_eq_actualParityCarrier (n : ℕ) :
    sourceParityIndices n = suzukiActualParityCarrier n := by
  ext m
  simp [sourceParityIndices, suzukiActualParityCarrier]
  omega


/-- A prime below the cubic cutoff has inherited logarithmic coordinate above two. -/
theorem caseII_raw_inherited_gt_two
    {D p : ℕ} (hp : 2 ≤ p) (hD : 1 < D)
    (hupper : (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ))) :
    2 < inheritedCoordinate D p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hloglt := Real.strictMonoOn_log (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    (show (D : ℝ) ^ (1 / (3 : ℝ)) ∈ Set.Ioi 0 by
      exact Real.rpow_pos_of_pos hDR _)
    hupper
  rw [Real.log_rpow hDR] at hloglt
  unfold inheritedCoordinate
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hlogp]
  norm_num [one_div] at hloglt ⊢
  nlinarith


end MathlibNt.SieveTheory
