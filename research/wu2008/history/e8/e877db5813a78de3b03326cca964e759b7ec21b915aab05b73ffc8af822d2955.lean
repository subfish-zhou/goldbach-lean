import W01ContinuousNodes

noncomputable section
namespace WuTarget.W01Continuous
open Set MeasureTheory QuarterTrim NodeExtension ActualNineFeedback Wu2008DoubleSieve
open scoped Classical

def continuousUniform (x : Fin 9 → ℝ) (t : ℝ) (v : ℝ × ℝ) : ℝ :=
  if v ∈ StaircaseShrink.domain t then kernel (hContinuous x) v.1 v.2 else 0

def continuousGamma (x : Fin 9 → ℝ) (t : ℝ) : ℝ :=
  4 * ∫ v : ℝ × ℝ, continuousUniform x t v

def continuousGain (x : Fin 9 → ℝ) : ℝ := continuousGamma x 0

def continuousBound (x : Fin 9 → ℝ) : ℝ :=
  hContinuous x 2 / (2*alpha^2*beta)

theorem continuousBound_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ continuousBound x :=
  div_nonneg (hContinuous_nonneg hx (by norm_num))
    (by have := alpha_pos; have := StaircaseShrink.fixed_bounds.1; positivity)

theorem u_bounds {v : ℝ × ℝ} (hv : v ∈ StaircaseShrink.domain 0) :
    u v.1 v.2 ∈ Icc 2 (41/10) := by
  refine ⟨?_,StaircaseShrink.original_u_upper hv⟩
  have h := (StaircaseShrink.domain_iff 0 v.1 v.2).mp hv
  apply (le_div_iff₀ alpha_pos).mpr
  linarith [h.2.2.2.2]

theorem continuous_kernel_bounds {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {v : ℝ × ℝ} (hv : v ∈ StaircaseShrink.domain 0) :
    0 ≤ kernel (hContinuous x) v.1 v.2 ∧
      kernel (hContinuous x) v.1 v.2 ≤ continuousBound x := by
  have hu := u_bounds hv
  have hd := DirectFiniteF6.denominator_bounds hv
  have hp := hContinuous_nonneg hx hu.2
  refine ⟨div_nonneg hp hd.1.le,?_⟩
  exact div_le_div₀ (hContinuous_nonneg hx (by norm_num))
    (hContinuous_antitone hx hu.1)
    (by have := alpha_pos; have := StaircaseShrink.fixed_bounds.1; positivity) hd.2

theorem measurable_continuous_kernel (x : Fin 9 → ℝ) :
    Measurable (fun v : ℝ × ℝ => kernel (hContinuous x) v.1 v.2) := by
  unfold kernel
  apply Measurable.div
  · apply (hContinuous_continuous x).measurable.comp
    unfold u
    fun_prop
  · fun_prop

theorem continuousUniform_integrable {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (continuousUniform x t) := by
  have hs := DirectFiniteF6.domain_measurable ht
  have hsub : StaircaseShrink.domain t ⊆ Icc alpha beta ×ˢ Icc beta (1/4) := by
    intro v hv
    have h := (StaircaseShrink.domain_iff t v.1 v.2).mp hv
    exact ⟨hv.1,h.2.2.1,by linarith [h.2.2.2.1]⟩
  apply (integrable_indicator_iff hs).mpr
  apply Measure.integrableOn_of_bounded (M := continuousBound x)
    (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top))
    (measurable_continuous_kernel x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with v hv
  have hb := continuous_kernel_bounds hx (StaircaseShrink.domain_subset ht hv)
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

theorem continuousUniform_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht : 0 ≤ t) (v : ℝ × ℝ) : 0 ≤ continuousUniform x t v := by
  unfold continuousUniform
  split_ifs with hv
  · exact (continuous_kernel_bounds hx (StaircaseShrink.domain_subset ht hv)).1
  · exact le_rfl

theorem continuousGain_nonneg {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ continuousGain x :=
  mul_nonneg (by norm_num) (integral_nonneg (continuousUniform_nonneg hx le_rfl))

theorem lowGain_le_continuousGain {x : Fin 9 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    WuTarget.W01.lowGain x ≤ continuousGain x := by
  apply mul_le_mul_of_nonneg_left
    (integral_mono (DirectFiniteF6.uniform_integrable _ le_rfl)
      (continuousUniform_integrable hx le_rfl) ?_) (by norm_num)
  intro v
  unfold DirectFiniteF6.uniform continuousUniform
  split_ifs with hv
  · exact div_le_div_of_nonneg_right (old_profile_le_continuous hx (u_bounds hv))
      (DirectFiniteF6.denominator_bounds hv).1.le
  · exact le_rfl

theorem continuousUniform_le_actual {x : Fin 9 → ℝ} {δ t : ℝ}
    (hn : ∀ i, 0 ≤ x i) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hx : ∀ i, x i ≤ actualNine δ i)
    (v : ℝ × ℝ) :
    continuousUniform x t v ≤ truncatedSixthMassHKernel δ v := by
  by_cases hv : v ∈ StaircaseShrink.domain t
  · have hvt : truncatedSixthLowerAdmissibleRegion t v.1 v.2 := by
      have he := congrArg (fun S : Set (ℝ × ℝ) => v ∈ S) (StaircaseActual.domain_eq ht.le)
      exact he.mp hv
    have hvd := StaircaseActual.region_mono (show δ ≤ t by linarith) hvt
    have hb := StaircaseShrink.source_budgets ht hδ hδt hv
    have hu := u_bounds (StaircaseShrink.domain_subset ht.le hv)
    have hs : StaircaseShrink.shiftedU δ v.1 v.2 ∈ Icc 2 (41/10) :=
      ⟨hb.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.trans hu.2⟩
    have hl : hContinuous x (u v.1 v.2) ≤
        wuImprovementLimit false δ (truncatedSixthLowerS δ v.1 v.2) :=
      (hContinuous_antitone hn hb.2.2.2.2.2.2.2).trans
        (hContinuous_le_actual hδ (by linarith) hx hs)
    rw [continuousUniform,if_pos hv,truncatedSixthMassHKernel,if_pos hvd]
    have hreg := truncatedSixthLower_region_bounds hδ.le hvd.1
    have hz : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤ v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hreg.1.le hreg.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    exact div_le_div₀ ((hContinuous_nonneg hn hu.2).trans hl) hl
      (StaircaseActual.denominator_pos hδ.le hvd) hz
  · rw [continuousUniform,if_neg hv]
    exact (truncatedSixthMass_kernels_bounds hδ (by linarith) v).2.1

theorem continuousGamma_payment {x : Fin 9 → ℝ} {δ t : ℝ}
    (hn : ∀ i, 0 ≤ x i) (ht : 0 < t) (ht' : t ≤ 1/1000)
    (hδ : 0 < δ) (hδt : δ ≤ t/2) (hx : ∀ i, x i ≤ actualNine δ i) :
    continuousGamma x t ≤ truncatedSixthLowerHadmdelta δ := by
  rw [continuousGamma,(truncatedSixthMass_literal_integrals hδ (by linarith)).2]
  exact mul_le_mul_of_nonneg_left
    (integral_mono (continuousUniform_integrable hn ht.le)
      (truncatedSixthMass_kernels_integrable hδ (by linarith)).2
      (continuousUniform_le_actual hn ht ht' hδ hδt hx)) (by norm_num)

end WuTarget.W01Continuous
