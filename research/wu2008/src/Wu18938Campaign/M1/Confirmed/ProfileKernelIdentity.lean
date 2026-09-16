import Wu18938Campaign.M1.Confirmed.ProfileFunctional
import MathlibNt.Wu2008DoubleSieve.MotherPairFeedbackMain
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalCoupledFeedback

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.ProfileGrid

open Wu2008DoubleSieve MotherPair Set Real MeasureTheory Filter
open scoped Classical Interval Topology

theorem kernel_integrable {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    Integrable (kernel p j H) := by
  have hs : Function.support (kernel p j H) ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro v hv
    have hr : v ∈ gainRegion p j := by
      by_contra hn
      exact hv (if_neg hn)
    have h := pairRegion_bounds hp j hr.1
    have he := gain_endpoint_order hp j
    exact ⟨⟨by linarith [h.1,he.1],by linarith [h.2.1,he.2.2.2.2.2.2]⟩,
      ⟨by linarith [h.1,h.2.2.1,he.1],by linarith [h.2.2.2,he.2.2.2.2.2.2]⟩⟩
  have hratio : Measurable (fun v : ℝ × ℝ => Hratio p j v.1 v.2) := by
    cases j <;> dsimp [Hratio] <;> fun_prop
  have hmeas : Measurable (kernel p j H) :=
    ((hm.comp hratio).mul (gain_smooth_continuous hp).measurable).ite
      (gain_region_measurable p j) measurable_const
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply Measure.integrableOn_of_bounded (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
    hmeas.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  change ‖kernel p j H v‖ ≤ 25 / (1 - 2 * (1 / p.kappa3))
  unfold kernel
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gain_smooth_bounds hp v).1]
    exact (mul_le_mul_of_nonneg_right (hb _) (gain_smooth_bounds hp v).1).trans
      (by simpa only [one_mul] using (gain_smooth_bounds hp v).2)
  · rw [norm_zero]
    exact (gain_smooth_bounds hp v).1.trans (gain_smooth_bounds hp v).2

theorem profile_pullback {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (1 / p.S) (upperP p j)) (v : ℝ) :
    H v * feedbackMasked p j v t =
      feedbackJac p j t * kernel p j H (t,feedbackU p j v t) := by
  unfold feedbackMasked kernel
  split_ifs with hr
  · have hb := pairRegion_bounds hp j hr.1
    rw [feedback_inverse_ratio hp j ht,
      gain_smooth_eq ⟨hb.1,hb.2.1⟩ ⟨hb.1.trans hb.2.2.1,hb.2.2.2⟩]
    dsimp [feedbackDensity]
    ring
  · simp

theorem profile_inner_substitution {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) (H : ℝ → ℝ) (t : ℝ) :
    (∫ u : ℝ, kernel p j H (t,u)) =
      ∫ v : ℝ, H v * feedbackMasked p j v t := by
  by_cases ht : t ∈ Icc (1 / p.S) (upperP p j)
  · have hJ := (feedback_jac_bounds hp j ht).1
    simp_rw [profile_pullback hp j H ht]
    rw [integral_const_mul]
    change _ = feedbackJac p j t * ∫ v : ℝ,
      (fun w => kernel p j H (t,(1-t)-w)) (feedbackJac p j t*v)
    rw [Measure.integral_comp_mul_left (fun w => kernel p j H (t,(1-t)-w)),smul_eq_mul,
      abs_of_pos (inv_pos.mpr hJ),
      integral_sub_left_eq_self (fun u => kernel p j H (t,u)) volume (1-t)]
    rw [← mul_assoc,mul_inv_cancel₀ hJ.ne',one_mul]
  · have hk (u : ℝ) : kernel p j H (t,u) = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff hp j t u).mp hr.1).1
    have hm (v : ℝ) : feedbackMasked p j v t = 0 := by
      apply if_neg
      exact fun hr => ht ((pairRegion_iff hp j t _).mp hr.1).1
    simp only [hk,hm,mul_zero,integral_zero]

theorem profile_feedback_log {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    (j : Term) {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∫ v : ℝ × ℝ, kernel p j H v) =
      ∫ v in (1 : ℝ)..3, H v * feedbackLogKernel p j v := by
  rw [show (∫ v : ℝ × ℝ, kernel p j H v) =
      ∫ t, ∫ u, kernel p j H (t,u) from integral_prod _ (kernel_integrable hp j hm hb)]
  simp_rw [profile_inner_substitution hp j H]
  rw [integral_integral_swap (f := fun t v => H v * feedbackMasked p j v t)
    (feedback_weighted_integrable hp j hm hb).swap]
  simp_rw [integral_const_mul]
  change (∫ v : ℝ, H v * feedbackKernel p j v) = _
  have hs : Function.support (fun v => H v * feedbackKernel p j v) ⊆ Icc (1 : ℝ) 3 := by
    intro v hv
    apply feedback_kernel_support hp j
    intro he
    exact hv (by simp only [he,mul_zero])
  rw [truncatedSixthMass_integral_eq_interval (by norm_num : (1 : ℝ) ≤ 3) hs]
  simp_rw [feedback_kernel_log hp j]

theorem four_profile_density {p : SecondFunctionalParameters} (hp : AnalyticParameters p)
    {H : ℝ → ℝ} (hm : Measurable H) (hb : ∀ v, |H v| ≤ 1) :
    (∑ j : Term, ∫ v : ℝ × ℝ, kernel p j H v) =
      ∫ v in (1 : ℝ)..3, H v * SecondFunctionalCoupledFeedback.density p v := by
  have hi (j : Term) :
      IntervalIntegrable (fun v => H v * feedbackLogKernel p j v) volume 1 3 := by
    simpa only [feedback_kernel_log hp j] using
      (feedback_kernel_weighted_integrable hp j hm hb).intervalIntegrable (a := 1) (b := 3)
  simp_rw [profile_feedback_log hp _ hm hb]
  rw [← intervalIntegral.integral_finsetSum (fun j _ => hi j)]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  rw [show (Finset.univ : Finset Term) =
      {Term.gammaFive,Term.gammaSix,Term.gammaSeven,Term.gammaEight} by ext j; cases j <;> simp]
  simp only [Finset.sum_insert (by decide : Term.gammaFive ∉
      {Term.gammaSix,Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSix ∉ {Term.gammaSeven,Term.gammaEight}),
    Finset.sum_insert (by decide : Term.gammaSeven ∉ {Term.gammaEight}),Finset.sum_singleton]
  unfold SecondFunctionalCoupledFeedback.density
  ring

end Wu18938Campaign.M1.Confirmed.ProfileGrid
