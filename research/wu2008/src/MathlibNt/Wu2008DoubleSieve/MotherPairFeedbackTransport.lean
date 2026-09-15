import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackKernel
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Genuine fixed-outer affine substitution and Fubini for all four mother terms. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real Filter MeasureTheory
open scoped Classical Topology Interval

theorem feedback_weighted_pullback {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ : ℝ) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) (v : ℝ) :
    gamma5GainH δ v * feedbackMasked p j v t =
      feedbackJac p j t * gainKernel p j δ (t,feedbackU p j v t) := by
  unfold feedbackMasked gainKernel
  split_ifs with hr
  · rw [feedback_inverse_ratio h j ht]
    dsimp [feedbackDensity]
    ring
  · simp

theorem feedback_inner_substitution {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) (δ t : ℝ) :
    (∫ u : ℝ, gainKernel p j δ (t,u)) =
      ∫ v : ℝ, gamma5GainH δ v * feedbackMasked p j v t := by
  by_cases ht : t ∈ Icc (1/p.S) (upperP p j)
  · have hJ := (feedback_jac_bounds h j ht).1
    simp_rw [feedback_weighted_pullback h j δ ht]
    rw [integral_const_mul]
    change _ = feedbackJac p j t * ∫ v : ℝ,
      (fun w => gainKernel p j δ (t,(1-t)-w)) (feedbackJac p j t*v)
    rw [Measure.integral_comp_mul_left (fun w => gainKernel p j δ (t,(1-t)-w)),smul_eq_mul,
      abs_of_pos (inv_pos.mpr hJ),
      integral_sub_left_eq_self (fun u => gainKernel p j δ (t,u)) volume (1-t)]
    rw [← mul_assoc,mul_inv_cancel₀ hJ.ne',one_mul]
  · have hg (u : ℝ) : gainKernel p j δ (t,u) = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff h j t u).mp hr.1).1
    have hm (v : ℝ) : feedbackMasked p j v t = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff h j t _).mp hr.1).1
    simp only [hg,hm,mul_zero,integral_zero]

theorem feedback_kernel_support {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) : Function.support (feedbackKernel p j) ⊆ Icc (1:ℝ) 3 := by
  intro v hv
  by_contra hn
  have he (t : ℝ) : feedbackMasked p j v t = 0 := by
    by_contra he
    exact hn (feedback_masked_support h j (a := (v,t)) he).1
  exact hv (by simp only [feedbackKernel,he,integral_zero])

/-- This consumes the imported actual two-dimensional gain producer. -/
theorem gainIntegral_feedback {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    gainIntegral p j δ =
      ∫ v in (1:ℝ)..3, wuImprovementLimit true δ v * feedbackKernel p j v := by
  have hm := (gamma5Gain_H_antitone hδ hδhi).measurable
  have hb : ∀ v, |gamma5GainH δ v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (gamma5Gain_H_bounds hδ hδhi v).1]
    exact (gamma5Gain_H_bounds hδ hδhi v).2
  rw [gain_integral_eq h j hδ hδhi]
  rw [show (∫ z : ℝ × ℝ, gainKernel p j δ z) = ∫ t, ∫ u, gainKernel p j δ (t,u) from
    integral_prod _ (gain_kernel_integrable h j hδ hδhi)]
  simp_rw [feedback_inner_substitution h j δ]
  rw [integral_integral_swap (f := fun t v => gamma5GainH δ v * feedbackMasked p j v t)
    (feedback_weighted_integrable h j hm hb).swap]
  simp_rw [integral_const_mul]
  change (∫ v : ℝ, gamma5GainH δ v * feedbackKernel p j v) = _
  have hs : Function.support (fun v => gamma5GainH δ v * feedbackKernel p j v) ⊆ Icc (1:ℝ) 3 := by
    intro v hv
    apply feedback_kernel_support h j
    intro he
    exact hv (by simp only [he,mul_zero])
  rw [truncatedSixthMass_integral_eq_interval (by norm_num : (1:ℝ) ≤ 3) hs]
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Icc (1:ℝ) 3 := by simpa only [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] using hv
  change gamma5GainH δ v * feedbackKernel p j v = _
  rw [gamma5GainH,gamma5Gain_clip_eq hv']

theorem feedback_actual_integrable {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    IntervalIntegrable (fun v => wuImprovementLimit true δ v * feedbackKernel p j v)
      volume 1 3 := by
  have hm := (gamma5Gain_H_antitone hδ hδhi).measurable
  have hb : ∀ v, |gamma5GainH δ v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (gamma5Gain_H_bounds hδ hδhi v).1]
    exact (gamma5Gain_H_bounds hδ hδhi v).2
  apply (feedback_kernel_weighted_integrable h j hm hb).intervalIntegrable.congr
  intro v hv
  have hv' : v ∈ Icc (1:ℝ) 3 := by
    simpa only [uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] using uIoc_subset_uIcc hv
  change gamma5GainH δ v * feedbackKernel p j v = _
  rw [gamma5GainH,gamma5Gain_clip_eq hv']

end Wu2008DoubleSieve.MotherPair
