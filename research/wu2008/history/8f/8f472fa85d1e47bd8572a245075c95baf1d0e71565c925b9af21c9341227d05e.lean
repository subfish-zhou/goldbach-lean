import SrcFifthGainActual

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

theorem weighted_profile_integrable {p : ℝ → ℝ} {M : ℝ} (hp : Measurable p)
    (hb : ∀ s ∈ Icc s0 FifthClassicalShape.q, |p s| ≤ M) :
    IntervalIntegrable (fun s => p s*weight s) volume s0 FifthClassicalShape.q := by
  have hi : IntegrableOn p (Icc s0 FifthClassicalShape.q) := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hp.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa only [Real.norm_eq_abs] using hb s hs
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le
    FifthClassicalShape.parameters.2.1.le).mpr hi
  apply hi'.mul_continuousOn
  rw [uIcc_of_le FifthClassicalShape.parameters.2.1.le]
  exact weight_continuous

theorem source_two_branches {p : ℝ → ℝ}
    (hi : Integrable (profileKernel p))
    (hw : IntervalIntegrable (fun s => p s*weight s) volume s0 FifthClassicalShape.q) :
    sourceGain p = 8*((∫ s in s0..geometricSplit, p s*lowerWeight s)+
      ∫ s in geometricSplit..FifthClassicalShape.q, p s*upperWeight s) := by
  have hp := fixed_breakpoints
  have hlg : s0 ≤ geometricSplit := by
    linarith [hp.2.2.2.1, hp.2.2.2.2.1]
  have hgq : geometricSplit ≤ FifthClassicalShape.q := hp.2.2.2.2.2.le
  have hi1 : IntervalIntegrable (fun s => p s*weight s) volume s0 geometricSplit := by
    apply hw.mono_set
    rw [uIcc_of_le hlg, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
    exact Icc_subset_Icc le_rfl hgq
  have hi2 : IntervalIntegrable (fun s => p s*weight s) volume geometricSplit FifthClassicalShape.q := by
    apply hw.mono_set
    rw [uIcc_of_le hgq, uIcc_of_le FifthClassicalShape.parameters.2.1.le]
    exact Icc_subset_Icc hlg le_rfl
  have he1 : (∫ s in s0..geometricSplit, p s*weight s) =
      ∫ s in s0..geometricSplit, p s*lowerWeight s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hlg] at hs
    rw [weight_lower hs]
  have he2 : (∫ s in geometricSplit..FifthClassicalShape.q, p s*weight s) =
      ∫ s in geometricSplit..FifthClassicalShape.q, p s*upperWeight s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hgq] at hs
    rw [weight_upper hs]
  rw [source_eq_scalar hi, scalarGain,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, he1, he2]

theorem actual_weighted_integrable {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    IntervalIntegrable (fun s => wuImprovementLimit false δ s*weight s)
      volume s0 FifthClassicalShape.q := by
  have hm : AntitoneOn (wuImprovementLimit false δ) (uIcc s0 FifthClassicalShape.q) := by
    apply (wuImprovementLimit_lower_antitone hδ (by linarith)).mono
    rw [uIcc_of_le FifthClassicalShape.parameters.2.1.le]
    exact fun _s hs => parameter_in_core hs
  apply hm.intervalIntegrable.mul_continuousOn
  rw [uIcc_of_le FifthClassicalShape.parameters.2.1.le]
  exact weight_continuous

theorem actual_source_two_branches {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/1000) :
    sourceGain (wuImprovementLimit false δ) =
      8*((∫ s in s0..geometricSplit, wuImprovementLimit false δ s*lowerWeight s)+
        ∫ s in geometricSplit..FifthClassicalShape.q, wuImprovementLimit false δ s*upperWeight s) :=
  source_two_branches (actual_kernel_integrable hδ hd) (actual_weighted_integrable hδ hd)

theorem grid_original_indices (h : ℕ → ℝ) :
    gridGain h = 8*∑ i ∈ Finset.Ico 15 28, cellWeight (i-15)*h i := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num only [Nat.reduceSub, Nat.add_sub_cancel_left]
  rfl

theorem cell_weight_directed {j : ℕ} (hj : j < 13) {w : ℝ → ℝ}
    (hi : IntervalIntegrable w volume (cellLower j) (cellUpper j))
    (hw : ∀ s ∈ Icc (cellLower j) (cellUpper j), w s ≤ weight s) :
    (∫ s in cellLower j..cellUpper j, w s) ≤ cellWeight j := by
  have hg := cell_geometry hj
  exact weight_integral_directed hg.1 hg.2.1 hg.2.2.1 hi hw

theorem cell_weight_error_lower {j : ℕ} (hj : j < 13) {w : ℝ → ℝ} {e : ℝ}
    (hi : IntervalIntegrable w volume (cellLower j) (cellUpper j))
    (hw : ∀ s ∈ Icc (cellLower j) (cellUpper j), w s-e ≤ weight s) :
    (∫ s in cellLower j..cellUpper j, w s)-(cellUpper j-cellLower j)*e ≤ cellWeight j := by
  have h := cell_weight_directed hj (hi.sub (intervalIntegrable_const (c := e))) hw
  rw [intervalIntegral.integral_sub hi (intervalIntegrable_const (c := e)),
    intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

end
end WuSource.SrcFifthGain
