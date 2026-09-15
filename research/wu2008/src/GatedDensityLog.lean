import GatedDensityGeometry

namespace GatedDensityPayment
open Wu2008DoubleSieve MotherPair Real Set MeasureTheory
open scoped Interval BigOperators
noncomputable section

def ratio (P L U : ℝ) : ℝ := U*(P-L)/(L*(P-U))

theorem ratio_pos {P L U : ℝ} (hL : 0<L) (hLU : L<U) (hUP : U<P) :
    0 < ratio P L U := by
  unfold ratio
  exact div_pos (mul_pos (hL.trans hLU) (by linarith))
    (mul_pos hL (by linarith))

theorem ratio_one_le {P L U : ℝ} (hL : 0<L) (hLU : L<U) (hUP : U<P) :
    1 ≤ ratio P L U := by
  unfold ratio
  apply (one_le_div (mul_pos hL (by linarith))).mpr
  nlinarith [mul_nonneg (hL.trans (hLU.trans hUP)).le (sub_nonneg.mpr hLU.le)]

theorem ratio_mono {P L U P₀ L₀ U₀ : ℝ}
    (hL : 0<L) (hLU : L<U) (hUP : U<P)
    (_hL₀ : 0<L₀) (hLU₀ : L₀<U₀) (hUP₀ : U₀<P₀)
    (hl : L ≤ L₀) (hu : U₀ ≤ U) (hp : P ≤ P₀) :
    ratio P₀ L₀ U₀ ≤ ratio P L U := by
  have hfirst : U₀/L₀ ≤ U/L := div_le_div₀ (by linarith) hu hL hl
  have hsecond : (P₀-L₀)/(P₀-U₀) ≤ (P-L)/(P-U) := by
    have hd : (U₀-L₀)/(P₀-U₀) ≤ (U-L)/(P-U) :=
      div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
    have he₀ : (P₀-L₀)/(P₀-U₀)=1+(U₀-L₀)/(P₀-U₀) := by
      field_simp [ne_of_gt (sub_pos.mpr hUP₀)]
      ring
    have he : (P-L)/(P-U)=1+(U-L)/(P-U) := by
      field_simp [ne_of_gt (sub_pos.mpr hUP)]
      ring
    rw [he₀,he]
    linarith
  have hmul := mul_le_mul hfirst hsecond
    (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) hL.le)
  simpa only [ratio,div_mul_div_comm] using hmul

theorem pole_antitone {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) :
    feedbackPole p j v ≤ feedbackPole p j a := by
  have hd := div_le_div_of_nonneg_right hav (by linarith [hp.three_le_S] : 0 ≤ p.S)
  have hr := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    (by linarith : 0<a+1) (by linarith : a+1 ≤ v+1)
  cases j <;> simp only [feedbackPole] <;> first | exact hr | linarith

theorem lower_pos {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (v : ℝ) : 0 < feedbackLower p j v := by
  have h : 0 < 1/p.S := one_div_pos.mpr (by linarith [hp.three_le_S])
  cases j <;> exact h.trans_le (le_max_left _ _)

theorem factor_lower {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {v b : ℝ} (hv : 1 ≤ v) (hvb : v ≤ b)
    (hP : 0 < feedbackPole p j v) : 1/b ≤ feedbackFactor p j v := by
  have hv0 : 0<v := by linarith

  have hdiv : 0 ≤ v/p.S := div_nonneg hv0.le (by linarith [hp.three_le_S])
  cases j <;> simp only [feedbackPole,feedbackFactor] at *
  all_goals apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
  all_goals first | exact hv0 | exact mul_pos hv0 hP | exact hvb | nlinarith [mul_nonneg hv0.le hdiv]

end
end GatedDensityPayment
