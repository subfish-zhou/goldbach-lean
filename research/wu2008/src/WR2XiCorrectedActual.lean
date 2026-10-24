import WR2XiCorrectedComparison

/-! The exact corrected matrix acts on the actual nine improvement values. -/
noncomputable section
namespace WuPaper.R2Xi
open Set MeasureTheory NodeExtension Wu2008DoubleSieve MotherPair ActualNineFeedback
open Wu2004MeanValue.GammaFiveLossBudget
open scoped Interval BigOperators

theorem Xi2_corrected_matrix_le_actual (r : Fin 4) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/10) :
    (∑ k : Fin 9, Xi2CorrectedCoefficient r k * actualNine δ k) ≤
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * Xi2 (gamma5OriginalRow r) t) -
      (∫ t in (1:ℝ)..3, wuImprovementLimit true δ t *
        generalKernel (rowParameters r).1 (rowParameters r).2 t) := by
  have hhalf : δ < 1/2 := by linarith
  have hz (k : Fin 9) : 0 ≤ actualNine δ k ∧ actualNine δ k ≤ 1 := by
    have h := gamma5Gain_H_bounds hd hhalf (upperNode k)
    simpa only [gamma5GainH, gamma5Gain_clip_eq (upperNode_bounds k), actualNine] using h
  have hfb (t : ℝ) : 0 ≤ nineProfile (actualNine δ) t ∧ nineProfile (actualNine δ) t ≤ 1 := by
    refine ⟨nineProfile_nonneg (fun k => (hz k).1) t, ?_⟩
    apply (le_abs_self _).trans
    exact nineProfile_abs_le_one _ (fun k => by rw [abs_of_nonneg (hz k).1]; exact (hz k).2) t
  have hgm := (gamma5Gain_H_antitone hd hhalf).measurable
  have hgi : IntervalIntegrable (gamma5GainH δ) volume 1 3 :=
    (gamma5Gain_H_antitone hd hhalf).intervalIntegrable
  have h := Xi2_corrected_integral_mono r (nineProfile_integrable _) hgi
    (nineProfile_measurable _) hgm hfb (gamma5Gain_H_bounds hd hhalf)
    (fun t ht => by
      simpa only [gamma5GainH, gamma5Gain_clip_eq ht] using nineProfile_le_actual hd hh ht)
  rw [Xi2_corrected_profile_expansion] at h
  have he (w : ℝ → ℝ) : (∫ t in (1:ℝ)..3, gamma5GainH δ t * w t) =
      ∫ t in (1:ℝ)..3, wuImprovementLimit true δ t * w t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)]
    intro t ht
    simp only [gamma5GainH, gamma5Gain_clip_eq ht]
  rw [he, he] at h
  exact h

/-- All original four rows with their exact nonnegative corrected matrix; no Gamma5 constant debit. -/
theorem Xi2_four_rows_corrected_matrix (r : Fin 4) {δ : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/10) :
    coupledBase (gamma5OriginalRow r) - deltaLoss δ * coupledLoss (gamma5OriginalRow r) +
      (∑ k : Fin 9, Xi2CorrectedCoefficient r k * actualNine δ k) ≤
      wuImprovementLimit true δ (gamma5OriginalRow r).s := by
  have h := Xi2_four_rows_exact_loss r hd hh
  have hm := Xi2_corrected_matrix_le_actual r hd hh
  linarith only [h, hm]

end WuPaper.R2Xi
