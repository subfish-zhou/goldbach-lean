import W07DensityBridge

noncomputable section
namespace WuTarget.W07
open Real Set MeasureTheory NodeExtension ActualNineFeedback Wu2008DoubleSieve MotherPair
open FiniteEndpointPayment GatedDensityPayment
open scoped Interval BigOperators

def rationalKernel (p : SecondFunctionalParameters) (j : Term) (a b : ℝ) : ℝ :=
  if feedbackLower p j a < min (feedbackUpper p j a) (feedbackUpper p j b) then
    (1 - (ratio (feedbackPole p j a) (feedbackLower p j a)
      (min (feedbackUpper p j a) (feedbackUpper p j b)))⁻¹) / b
  else 0

theorem rationalKernel_bounds {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ rationalKernel p j a b ∧ rationalKernel p j a b ≤ kernelEndpoint p j a b := by
  unfold rationalKernel kernelEndpoint
  split_ifs with hg
  · have hU := (feedback_pole_geometry hp j ⟨ha, hab.trans hb⟩
      ⟨(hg.trans_le (min_le_left _ _)).le, le_rfl⟩).2
    have hP : min (feedbackUpper p j a) (feedbackUpper p j b) < feedbackPole p j a :=
      (min_le_left _ _).trans_lt hU
    have hR := ratio_pos (lower_pos hp j a) hg hP
    have hR1 := ratio_one_le (lower_pos hp j a) hg hP
    have hrec : (ratio (feedbackPole p j a) (feedbackLower p j a)
        (min (feedbackUpper p j a) (feedbackUpper p j b)))⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hR1)
    exact ⟨div_nonneg (sub_nonneg.mpr hrec) (by linarith),
      div_le_div_of_nonneg_right (one_sub_inv_le_log_of_pos hR) (by linarith)⟩
  · exact ⟨le_rfl, le_rfl⟩

def rationalDensity (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  rationalKernel p .gammaFive a b + rationalKernel p .gammaSix a b +
    rationalKernel p .gammaSeven a b + rationalKernel p .gammaEight a b

theorem rationalDensity_bounds {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ rationalDensity p a b ∧ rationalDensity p a b ≤ densityEndpoint p a b := by
  have h5 := rationalKernel_bounds hp .gammaFive ha hab hb
  have h6 := rationalKernel_bounds hp .gammaSix ha hab hb
  have h7 := rationalKernel_bounds hp .gammaSeven ha hab hb
  have h8 := rationalKernel_bounds hp .gammaEight ha hab hb
  exact ⟨add_nonneg (add_nonneg (add_nonneg h5.1 h6.1) h7.1) h8.1,
    add_le_add (add_le_add (add_le_add h5.2 h6.2) h7.2) h8.2⟩

def rationalInterval (p : SecondFunctionalParameters) (a b : ℝ) : ℝ :=
  (firstSplit p a b - a) * rationalDensity p a (firstSplit p a b) +
    (secondSplit p a b - firstSplit p a b) *
      rationalDensity p (firstSplit p a b) (secondSplit p a b) +
    (b - secondSplit p a b) * rationalDensity p (secondSplit p a b) b

theorem rationalInterval_bounds {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    0 ≤ rationalInterval p a b ∧ rationalInterval p a b ≤ intervalPayment p a b := by
  have ho := split_order p hab
  have h0 := rationalDensity_bounds hp ha ho.1 (ho.2.1.trans (ho.2.2.trans hb))
  have h1 := rationalDensity_bounds hp (ha.trans ho.1) ho.2.1 (ho.2.2.trans hb)
  have h2 := rationalDensity_bounds hp (ha.trans (ho.1.trans ho.2.1)) ho.2.2 hb
  exact ⟨add_nonneg (add_nonneg
    (mul_nonneg (sub_nonneg.mpr ho.1) h0.1)
    (mul_nonneg (sub_nonneg.mpr ho.2.1) h1.1))
    (mul_nonneg (sub_nonneg.mpr ho.2.2) h2.1),
    add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left h0.2 (sub_nonneg.mpr ho.1))
      (mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.mpr ho.2.1)))
      (mul_le_mul_of_nonneg_left h2.2 (sub_nonneg.mpr ho.2.2))⟩

def rationalEntry (p : SecondFunctionalParameters) (k : Fin 9) : ℝ :=
  rationalInterval p (left 1 3 k) (right 1 3 k) / 5

theorem rationalEntry_bounds (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (k : Fin 9) : 0 ≤ rationalEntry p k ∧ rationalEntry p k ≤ logEntry p k := by
  have h := rationalInterval_bounds hp (clip_bounds (by norm_num : (1 : ℝ) ≤ 3)).1
    (cell_order 1 3 k) (clip_bounds (by norm_num : (1 : ℝ) ≤ 3)).2
  exact ⟨div_nonneg h.1 (by norm_num), div_le_div_of_nonneg_right h.2 (by norm_num)⟩

theorem rationalEntry_le_densityEntry (p : SecondFunctionalParameters)
    (hp : AnalyticParameters p) (k : Fin 9) : rationalEntry p k ≤ densityEntry p k :=
  (rationalEntry_bounds p hp k).2.trans (logEntry_le_densityEntry p hp k)

theorem rationalEntry_sum_le (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (z : Fin 9 → ℝ) (hz : ∀ k, 0 ≤ z k) :
    (∑ k : Fin 9, rationalEntry p k * z k) ≤ densityMoment p z / 5 := by
  rw [densityMoment_eq_sum p hp]
  exact Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_right (rationalEntry_le_densityEntry p hp k) (hz k))

end WuTarget.W07
