import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplaceDerivative

/-! The actual exponential moment, by translation and one-dimensional FTC. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real LiLiuPrereqBuchstab
open scoped Topology

/-- Translation preserves the actual delayed Laplace integrability. -/
theorem buchstabLaplace_delay_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun u : ℝ => buchstab (u - 1) * exp (-z * u)) (Ioi 2) := by
  have hp : (fun u : ℝ => u + (-1)) ⁻¹' Ioi 1 = Ioi 2 := by
    ext u
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have h := ((measurePreserving_add_right volume (-1 : ℝ)).integrableOn_comp_preimage
    (Homeomorph.addRight (-1 : ℝ)).measurableEmbedding).mpr (buchstabLaplace_integrable hz)
  rw [hp] at h
  have hc : IntegrableOn
      (fun u : ℝ => exp (-z) * (buchstab (u + (-1)) * exp (-z * (u + (-1)))))
      (Ioi 2) := h.const_mul (exp (-z))
  apply hc.congr_fun _ measurableSet_Ioi
  intro u _hu
  dsimp [Function.comp]
  rw [← mul_assoc, mul_comm (exp (-z)), mul_assoc, ← exp_add]
  congr 2
  ring

/-- The delayed integral is the literal original transform times its exponential shift. -/
theorem buchstabLaplace_delay_integral (z : ℝ) :
    (∫ u : ℝ in Ioi 2, buchstab (u - 1) * exp (-z * u)) =
      exp (-z) * buchstabLaplace z := by
  have hp : (fun u : ℝ => u + (-1)) ⁻¹' Ioi 1 = Ioi 2 := by
    ext u
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have h := (measurePreserving_add_right volume (-1 : ℝ)).setIntegral_preimage_emb
    (Homeomorph.addRight (-1 : ℝ)).measurableEmbedding
    (fun v : ℝ => buchstab v * exp (-z * v)) (Ioi 1)
  rw [hp] at h
  rw [buchstabLaplace, ← h, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _hu
  dsimp
  rw [← mul_assoc (exp (-z)), mul_comm (exp (-z)), mul_assoc, ← exp_add]
  congr 2
  ring

/-- The true weighted Buchstab boundary at infinity vanishes. -/
theorem buchstabLaplace_moment_boundary {z : ℝ} (hz : 0 < z) :
    Tendsto (fun u : ℝ => u * buchstab u * exp (-z * u)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun u : ℝ => u * exp (-z * u))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := le_trans (by norm_num) hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (mul_nonneg hu0 (buchstab_nonneg hu)) (exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hu0 (buchstab_le_one hu)) (exp_pos _).le
  · simpa only [rpow_one, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z hz

/-- FTC on the regular open tail, with continuity (not differentiability) at two. -/
theorem buchstabLaplace_moment_tail {z : ℝ} (hz : 0 < z) :
    exp (-z) * buchstabLaplace z -
      z * (∫ u : ℝ in Ioi 2, u * buchstab u * exp (-z * u)) = -exp (-z * 2) := by
  have hm := (buchstabLaplace_moment_integrable hz).mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have hd : ∀ u ∈ Ioi (2 : ℝ), HasDerivAt
      (fun u : ℝ => u * buchstab u * exp (-z * u))
      (buchstab (u - 1) * exp (-z * u) - z * (u * buchstab u * exp (-z * u))) u := by
    intro u hu
    convert! (hasDerivAt_mul_buchstab hu).mul
      (((hasDerivAt_id u).const_mul (-z)).exp) using 1
    dsimp
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (((continuous_id.mul continuous_buchstab).mul
      (continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt.continuousWithinAt)
    hd ((buchstabLaplace_delay_integrable hz).sub (hm.const_mul z))
    (buchstabLaplace_moment_boundary hz)
  rw [integral_sub (buchstabLaplace_delay_integrable hz) (hm.const_mul z),
    integral_const_mul, buchstabLaplace_delay_integral] at hi
  change _ = 0 - (2 * buchstab 2 * exp (-z * 2)) at hi
  rw [buchstab_history_identity (by norm_num : (1 : ℝ) ≤ 2) le_rfl] at hi
  simpa using hi

/-- The history moment is evaluated by its exact elementary primitive. -/
theorem buchstabLaplace_moment_history (z : ℝ) :
    z * (∫ u : ℝ in (1 : ℝ)..2, u * buchstab u * exp (-z * u)) =
      exp (-z) - exp (-z * 2) := by
  have he : (∫ u : ℝ in (1 : ℝ)..2, u * buchstab u * exp (-z * u)) =
      ∫ u : ℝ in (1 : ℝ)..2, exp (-z * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
    dsimp
    rw [buchstab_history_identity hu.1 hu.2, one_mul]
  rw [he, ← intervalIntegral.integral_const_mul]
  have hd : ∀ u ∈ uIcc (1 : ℝ) 2,
      HasDerivAt (fun u : ℝ => -exp (-z * u)) (z * exp (-z * u)) u := by
    intro u _hu
    convert! (((hasDerivAt_id u).const_mul (-z)).exp).neg using 1
    dsimp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 1 2)
  simpa only [mul_one, neg_sub_neg] using hi

/-- The original first exponential moment, with no supplied moment identity. -/
theorem buchstabLaplace_moment_identity {z : ℝ} (hz : 0 < z) :
    z * (∫ u : ℝ in Ioi 1, u * buchstab u * exp (-z * u)) =
      exp (-z) * (1 + buchstabLaplace z) := by
  have hm := buchstabLaplace_moment_integrable hz
  have hs := intervalIntegral.integral_interval_add_Ioi hm
    (hm.mono_set (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2)))
  have ht := buchstabLaplace_moment_tail hz
  have hh := buchstabLaplace_moment_history z
  rw [← hs]
  nlinarith [ht, hh]

end Wu2008DoubleSieve.SecondFunctionalJointTail
