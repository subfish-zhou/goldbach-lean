import Wu08Staircase
import Mathlib.MeasureTheory.Integral.Prod

open Set MeasureTheory QuarterTrim

namespace Wu08Staircase

theorem measurable_kernel : Measurable (fun v : ℝ × ℝ => kernel profile v.1 v.2) := by
  unfold kernel
  apply Measurable.div
  · apply measurable_profile.comp
    unfold u
    fun_prop
  · fun_prop

theorem inner_integrable (x : ℝ) (hx : x ∈ Icc alpha (alpha + d)) :
    IntervalIntegrable (kernel profile x) volume (1 / 4) (top x) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (top_ge hx)).2
  apply Measure.integrableOn_of_bounded (M := 2 * q / alpha ^ 2)
    (measure_Icc_lt_top.ne)
    ((measurable_kernel.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  change ‖kernel profile x y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_bounds ⟨hx, hy⟩ (profile_bounds _)).1]
  exact (kernel_bounds ⟨hx, hy⟩ (profile_bounds _)).2

/-- The two-variable kernel itself is integrable on the actual closed triangle. -/
theorem triangle_integrable : IntegrableOn
    (fun v : ℝ × ℝ => kernel profile v.1 v.2) {v | triangle v.1 v.2} volume := by
  have hs : MeasurableSet {v : ℝ × ℝ | triangle v.1 v.2} := by
    unfold triangle top
    apply MeasurableSet.inter
    · exact measurableSet_Icc.preimage measurable_fst
    · apply MeasurableSet.inter
      · exact measurableSet_le measurable_const measurable_snd
      · apply measurableSet_le measurable_snd
        fun_prop
  have hsub : {v : ℝ × ℝ | triangle v.1 v.2} ⊆
      Icc alpha (alpha + d) ×ˢ Icc (1 / 4) (top alpha) := by
    intro v hv
    refine ⟨hv.1, hv.2.1, ?_⟩
    have hyt := hv.2.2
    dsimp [top] at hyt ⊢
    linarith [hv.1.1]
  apply Measure.integrableOn_of_bounded (M := 2 * q / alpha ^ 2)
    (ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top))
    measurable_kernel.aestronglyMeasurable
  filter_upwards [ae_restrict_mem hs] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (kernel_bounds hv (profile_bounds _)).1]
  exact (kernel_bounds hv (profile_bounds _)).2

/-- Globally measurable extension of the actual inner integral on the excess triangle. -/
noncomputable def sectionIntegral (x : ℝ) : ℝ :=
  ∫ y : ℝ, (Ioc (1 / 4) (top x)).indicator (kernel profile x) y

theorem measurable_sectionIntegral : Measurable sectionIntegral := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  classical
  unfold Function.uncurry Set.indicator
  apply Measurable.ite _ measurable_kernel measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_lt measurable_const measurable_snd
  · apply measurableSet_le measurable_snd
    unfold top
    fun_prop

theorem sectionIntegral_eq (x : ℝ) (hx : x ∈ Icc alpha (alpha + d)) :
    sectionIntegral x = ∫ y in (1 / 4)..top x, kernel profile x y := by
  rw [intervalIntegral.integral_of_le (top_ge hx)]
  exact integral_indicator measurableSet_Ioc

theorem sectionIntegral_bounds (x : ℝ) (hx : x ∈ Icc alpha (alpha + d)) :
    0 ≤ sectionIntegral x ∧ sectionIntegral x ≤ d * (2 * q / alpha ^ 2) := by
  rw [sectionIntegral_eq x hx]
  constructor
  · apply intervalIntegral.integral_nonneg (top_ge hx)
    intro y hy
    exact (kernel_bounds ⟨hx, hy⟩ (profile_bounds _)).1
  · have hb := intervalIntegral.integral_mono_on (top_ge hx)
      (inner_integrable x hx) (intervalIntegrable_const (c := 2 * q / alpha ^ 2))
      (fun y hy => (kernel_bounds ⟨hx, hy⟩ (profile_bounds _)).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hb
    have hl : top x - 1 / 4 ≤ d := by
      dsimp [top, d]
      linarith [hx.1]
    exact hb.trans (mul_le_mul_of_nonneg_right hl
      (div_nonneg (mul_nonneg (by norm_num) (le_of_lt q_pos)) (sq_nonneg alpha)))

theorem outer_integrable : IntervalIntegrable
    (fun x => ∫ y in (1 / 4)..top x, kernel profile x y) volume alpha (alpha + d) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by linarith [d_pos] : alpha ≤ alpha + d)).2
  have hi : IntegrableOn sectionIntegral (Icc alpha (alpha + d)) volume := by
    apply Measure.integrableOn_of_bounded (M := d * (2 * q / alpha ^ 2))
      measure_Icc_lt_top.ne measurable_sectionIntegral.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sectionIntegral_bounds x hx).1]
    exact (sectionIntegral_bounds x hx).2
  apply hi.congr_fun _ measurableSet_Icc
  intro x hx
  exact sectionIntegral_eq x hx

/-- No profile, boundedness, or integrability hypotheses remain. -/
theorem loss_bounds : 0 ≤ loss profile ∧ loss profile ≤ 4 * q * (d / alpha) ^ 2 :=
  QuarterTrim.loss_bounds profile triangle_profile_bounds inner_integrable outer_integrable

theorem coefficient_loss_bounds :
    0 ≤ loss profile / 4 ∧ loss profile / 4 ≤ 3403880289 / 1600000000000 := by
  have hb := loss_bounds
  have he := exact_coefficient_loss
  unfold coefficientLoss at he
  constructor <;> linarith

/-- The remaining base hypothesis is the original uncertified aggregate, not a profile seam. -/
theorem conditional_coefficient (base : ℝ) (hb : printedSum ≤ base) :
    (899 / 1000 : ℝ) < base - loss profile / 4 :=
  conditional_coefficient_of_integral profile base hb
    triangle_profile_bounds inner_integrable outer_integrable

theorem printed_margin_lower_bound :
    9604119711 / 1600000000000 ≤ printedSum - loss profile / 4 - 899 / 1000 := by
  have hb := coefficient_loss_bounds
  norm_num [printedSum] at *
  linarith

end Wu08Staircase
