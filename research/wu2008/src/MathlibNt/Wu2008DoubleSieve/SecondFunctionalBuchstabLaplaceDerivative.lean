import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplace
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabEuler

/-! Local dominated differentiation of the literal Laplace integral. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real LiLiuPrereqBuchstab
open scoped Topology

/-- A fixed positive half-parameter dominates all derivatives on a neighborhood. -/
theorem buchstabLaplace_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt buchstabLaplace
      (-(∫ u : ℝ in Ioi 1, u * buchstab u * exp (-z * u))) z := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (E := ℝ)
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun z u : ℝ => buchstab u * exp (-z * u))
    (F' := fun z u : ℝ => -(u * buchstab u * exp (-z * u)))
    (bound := fun u : ℝ => u * buchstab u * exp (-(z / 2) * u))
    (s := Ioi (z / 2))
    (Ioi_mem_nhds (by linarith : z / 2 < z))
    (Eventually.of_forall fun w =>
      (continuous_buchstab.mul (continuous_exp.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (buchstabLaplace_integrable hz)
    (((continuous_id.mul continuous_buchstab).mul (continuous_exp.comp
      (continuous_const.mul continuous_id))).neg.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      change 1 < u at hu
      change z / 2 < w at hw
      have hu0 : 0 ≤ u := by linarith [hu]
      have hb := buchstab_nonneg hu.le
      change ‖-(u * buchstab u * exp (-w * u))‖ ≤ _
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hu0 hb)
      apply exp_le_exp.mpr
      nlinarith [hw])
    (buchstabLaplace_moment_integrable (half_pos hz))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _hu
      intro w _hw
      convert! ((((hasDerivAt_id w).neg).mul_const u).exp.const_mul (buchstab u)) using 1
      dsimp
      ring)
  convert! h.2 using 1
  simp only [integral_neg]

/-- The normalization at large positive parameters follows from the actual integral bound. -/
theorem buchstabLaplace_tendsto_atTop : Tendsto buchstabLaplace atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun z : ℝ => z⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (buchstabLaplace_nonneg z)]
    apply (buchstabLaplace_le hz).trans
    rw [← one_div]
    exact div_le_div_of_nonneg_right (exp_le_one_iff.mpr (neg_nonpos.mpr hz.le)) hz.le
  · exact tendsto_inv_atTop_zero

/-- The exponential-integral tail vanishes at infinity. -/
theorem buchstabE1_tendsto_atTop : Tendsto buchstabE1 atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

/-- The derivative of the actual exponential integral on its positive domain. -/
theorem buchstabE1_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt buchstabE1 (-(exp (-z) / z)) z := by
  let f : ℝ → ℝ := fun t => exp (-t) / t
  have hcont : ContinuousAt f z :=
    ((continuous_exp.comp continuous_neg).continuousAt).div continuousAt_id (ne_of_gt hz)
  have hi : IntervalIntegrable f volume z z := IntervalIntegrable.refl
  have hd := (intervalIntegral.integral_hasDerivAt_right hi
    (((measurable_exp.comp measurable_neg).div measurable_id).stronglyMeasurable.stronglyMeasurableAtFilter) hcont).const_sub (buchstabE1 z)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hz] with w hw
  have he := intervalIntegral.integral_Ioi_sub_Ioi'
    (buchstabE1_integrable hz) (buchstabE1_integrable hw)
  change buchstabE1 w = buchstabE1 z - ∫ t : ℝ in z..w, f t
  change buchstabE1 z - buchstabE1 w = ∫ t : ℝ in z..w, f t at he
  linarith

end Wu2008DoubleSieve.SecondFunctionalJointTail
