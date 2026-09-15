import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabTailSlope
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The literal Buchstab Laplace integral and its analytic convergence.
The frozen Buchstab construction is reused, not reconstructed here. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real LiLiuPrereqBuchstab
open scoped Topology

noncomputable def buchstabLaplace (z : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 1, buchstab u * exp (-z * u)

/-- The actual integrated delay equation, with the delay removed by translation. -/
theorem buchstab_integral_identity {u : ℝ} (hu : 2 ≤ u) :
    u * buchstab u = 1 + ∫ v : ℝ in 1..u - 1, buchstab v := by
  rw [mul_buchstab_eq_integral hu, intervalIntegral.integral_comp_sub_right]
  norm_num

/-- The history contributes exactly one, including both endpoints. -/
theorem buchstab_history_identity {u : ℝ} (hu : 1 ≤ u) (hu' : u ≤ 2) :
    u * buchstab u = 1 := by
  rw [buchstab_eq_one_div hu hu']
  field_simp

/-- A single formula on the entire Laplace integration domain. -/
theorem buchstab_integral_identity_full {u : ℝ} (hu : 1 ≤ u) :
    u * buchstab u =
      1 + if 2 ≤ u then ∫ v : ℝ in 1..u - 1, buchstab v else 0 := by
  split_ifs with h
  · exact buchstab_integral_identity h
  · simpa using buchstab_history_identity hu (le_of_lt (not_le.mp h))

theorem buchstabLaplace_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => buchstab u * exp (-z * u)) (Ioi 1) := by
  apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) 1).mono'
    ((continuous_buchstab.mul (continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  change ‖buchstab u * exp (-z * u)‖ ≤ exp (-z * u)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (buchstab_nonneg hu.le) (exp_pos _).le)]
  exact mul_le_of_le_one_left (exp_pos _).le (buchstab_le_one hu.le)

theorem buchstabLaplace_nonneg (z : ℝ) : 0 ≤ buchstabLaplace z := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (buchstab_nonneg hu.le) (exp_pos _).le

theorem buchstabLaplace_le {z : ℝ} (hz : 0 < z) :
    buchstabLaplace z ≤ exp (-z) / z := by
  have h := integral_mono_ae (buchstabLaplace_integrable hz)
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) 1) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_le_of_le_one_left (exp_pos _).le (buchstab_le_one hu.le))
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hz)] at h
  simpa [buchstabLaplace] using h

/-- The first exponential moment is genuinely integrable. -/
theorem buchstabLaplace_moment_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => u * buchstab u * exp (-z * u)) (Ioi 1) := by
  have hbase : IntegrableOn (fun u : ℝ => u * exp (-z * u)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := 1) (p := 1) (by norm_num) le_rfl hz)
  apply (hbase.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mono'
    ((continuous_id.mul continuous_buchstab).mul
      (continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu.le
  change ‖u * buchstab u * exp (-z * u)‖ ≤ u * exp (-z * u)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (mul_nonneg hu0 (buchstab_nonneg hu.le)) (exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right hu0 (buchstab_le_one hu.le)) (exp_pos _).le

end Wu2008DoubleSieve.SecondFunctionalJointTail
