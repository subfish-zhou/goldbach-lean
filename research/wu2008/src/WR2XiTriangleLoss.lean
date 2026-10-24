import WR2XiLossCell

/-! Exact first-cell correction for the literal full and legal Gamma5 triangles. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory NodeExtension
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval BigOperators

theorem nineProfile_measurable (z : Fin 9 → ℝ) : Measurable (nineProfile z) := by
  unfold nineProfile
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.indicator measurableSet_Ioc

theorem nineProfile_abs_le_one (z : Fin 9 → ℝ) (hz : ∀ k, |z k| ≤ 1)
    (t : ℝ) : |nineProfile z t| ≤ 1 := by
  classical
  by_cases h : ∃ k, t ∈ Ioc (upperLeft k) (upperNode k)
  · obtain ⟨k, hk⟩ := h
    rw [nineProfile_cell z hk]
    exact hz k
  · have he : nineProfile z t = 0 := by
      unfold nineProfile
      apply Finset.sum_eq_zero
      intro k _
      exact indicator_of_notMem (fun hk => h ⟨k, hk⟩) _
    rw [he]
    norm_num

/-- Exact loss for any bounded measurable weight, with the original normalization. -/
theorem gamma5_triangle_loss_identity (r : Fin 4) (H : ℝ → ℝ)
    (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (triangleGain (rowParameters r).1 (rowParameters r).2 false H -
      triangleGain (rowParameters r).1 (rowParameters r).2 true H)/5 =
      ∫ v in (1:ℝ)..3, H v * generalKernel (rowParameters r).1 (rowParameters r).2 v := by
  have hp : 0 < (rowParameters r).1 ∧ 1/3 ≤ (rowParameters r).2 ∧
      (rowParameters r).2 < 1/2 ∧
      1/(rowParameters r).1 ≤ (rowParameters r).2 ∧
      5/4 ≤ (rowParameters r).1*(1-2*(rowParameters r).2) ∧
      (rowParameters r).1 ≤ 5 := by
    fin_cases r <;> norm_num [rowParameters]
  have hf := triangle_literal_log hp.1 hp.2.2.1 hp.2.2.2.1
    (by linarith [hp.2.2.2.2.1]) hp.2.2.2.2.2 false hm hb
  have hl := triangle_literal_log hp.1 hp.2.2.1 hp.2.2.2.1
    (by linarith [hp.2.2.2.2.1]) hp.2.2.2.2.2 true hm hb
  change triangleGain _ _ false H = _ at hf
  change triangleGain _ _ true H = _ at hl
  have hfi := (triangle_log_integrable hp.1 hp.2.2.1 false hm hb).intervalIntegrable
    (a := (1:ℝ)) (b := 3)
  have hli := (triangle_log_integrable hp.1 hp.2.2.1 true hm hb).intervalIntegrable
    (a := (1:ℝ)) (b := 3)
  rw [hf, hl, ← intervalIntegral.integral_sub hfi hli]
  simp only [Bool.false_eq_true, if_false, if_true, ← mul_sub]
  rw [weighted_section_loss_identity hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.1]
  ring

/-- The exact missing triangle is one scalar times the first node. -/
theorem gamma5_triangle_profile_loss (r : Fin 4) (z : Fin 9 → ℝ)
    (hz : ∀ k, |z k| ≤ 1) :
    (triangleGain (rowParameters r).1 (rowParameters r).2 false (nineProfile z) -
      triangleGain (rowParameters r).1 (rowParameters r).2 true (nineProfile z))/5 =
      z 0 * gamma5CellLoss r := by
  rw [gamma5_triangle_loss_identity r _ (nineProfile_measurable z)
    (nineProfile_abs_le_one z hz), gamma5_profile_loss]

/-- The same identity for the actual final-depth improvement, without a uniform debit. -/
theorem gamma5_triangle_actual_loss (r : Fin 4) {δ : ℝ}
    (hd : 0 < δ) (hh : δ < 1/2) :
    (triangleGain (rowParameters r).1 (rowParameters r).2 false
        (Wu2008DoubleSieve.wuImprovementLimit true δ) -
      triangleGain (rowParameters r).1 (rowParameters r).2 true
        (Wu2008DoubleSieve.wuImprovementLimit true δ))/5 =
      ∫ v in (1:ℝ)..3, Wu2008DoubleSieve.wuImprovementLimit true δ v *
        generalKernel (rowParameters r).1 (rowParameters r).2 v := by
  have hb (v : ℝ) : |Wu2008DoubleSieve.gamma5GainH δ v| ≤ 1 := by
    have h := Wu2008DoubleSieve.gamma5Gain_H_bounds hd hh v
    rw [abs_of_nonneg h.1]
    exact h.2
  have he := gamma5_triangle_loss_identity r (Wu2008DoubleSieve.gamma5GainH δ)
    (Wu2008DoubleSieve.gamma5Gain_H_antitone hd hh).measurable hb
  simp only [Wu2008DoubleSieve.gamma5_row_triangle_unclip] at he
  rw [he]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  intro v hv
  simp only [Wu2008DoubleSieve.gamma5GainH, Wu2008DoubleSieve.gamma5Gain_clip_eq hv]

end WuPaper.R2Xi
