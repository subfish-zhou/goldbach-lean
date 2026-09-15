import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplace
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalEulerLogMoment
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Euler normalization for the actual exponential integral. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter MeasureTheory Real Asymptotics
open scoped Topology

noncomputable def buchstabE1 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ioi z, exp (-t) / t

/-- The Mellin derivative convergence theorem supplies absolute integrability. -/
theorem euler_log_moment_integrable :
    IntegrableOn (fun t : ℝ => log t * exp (-t)) (Ioi 0) := by
  have h := (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
    (f := fun t : ℝ => (exp (-t) : ℂ)) (a := 2) (b := 0) (s := 1)
    (by
      apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
      exact (Complex.continuous_ofReal.comp (continuous_exp.comp continuous_neg)).continuousOn)
    (by
      rw [← isBigO_norm_left]
      simp_rw [Complex.norm_real, isBigO_norm_left]
      simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-2)).isBigO)
    (by norm_num)
    (by
      simp_rw [neg_zero, rpow_zero]
      refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
      have hc : Tendsto (fun t : ℝ => ((exp (-t) : ℝ) : ℂ)) (𝓝[>] 0)
          (𝓝 ((exp (-0) : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_exp.comp continuous_neg)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      simpa only [neg_zero, exp_zero, Complex.ofReal_one] using hc)
    (by norm_num)).1
  have hc : IntegrableOn (fun t : ℝ => ((log t * exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
    simpa [MellinConvergent, smul_eq_mul, Complex.ofReal_mul] using h
  exact hc.re

theorem buchstabE1_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp (-t) / t) (Ioi z) := by
  have he : IntegrableOn (fun t : ℝ => exp (-t)) (Ioi z) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) z
  apply (he.div_const z).mono'
    (((continuousOn_exp.comp continuousOn_neg (fun _ _ => mem_univ _)).div
      continuousOn_id (fun t ht => ne_of_gt (hz.trans ht))).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖exp (-t) / t‖ ≤ exp (-t) / z
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (exp_pos _) (hz.trans ht))]
  exact div_le_div_of_nonneg_left (exp_pos _).le hz ht.le

/-- The integration-by-parts boundary at infinity vanishes, without numerical estimates. -/
theorem euler_log_exp_boundary :
    Tendsto (fun t : ℝ => log t * exp (-t)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => t * exp (-t))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (log_nonneg ht) (exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith))
      (exp_pos _).le
  · simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

/-- Integration by parts on the positive half-line, with its actual boundary. -/
theorem buchstabE1_log_identity {z : ℝ} (hz : 0 < z) :
    buchstabE1 z + log z = (1 - exp (-z)) * log z +
      ∫ t : ℝ in Ioi z, log t * exp (-t) := by
  have hm := euler_log_moment_integrable.mono_set (Ioi_subset_Ioi hz.le)
  have hd : ∀ t ∈ Ioi z, HasDerivAt (fun t : ℝ => log t * exp (-t))
      (exp (-t) / t - log t * exp (-t)) t := by
    intro t ht
    convert! (hasDerivAt_log (ne_of_gt (hz.trans ht))).mul
      ((hasDerivAt_id t).neg.exp) using 1
    dsimp
    ring
  have hcont : ContinuousWithinAt (fun t : ℝ => log t * exp (-t)) (Ici z) z :=
    ((continuousAt_log (ne_of_gt hz)).mul
      (continuous_exp.comp continuous_neg).continuousAt).continuousWithinAt
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd
    ((buchstabE1_integrable hz).sub hm) euler_log_exp_boundary
  rw [integral_sub (buchstabE1_integrable hz) hm] at hi
  change buchstabE1 z - (∫ t : ℝ in Ioi z, log t * exp (-t)) = _ at hi
  linarith

/-- The logarithmic moment tail converges to the already identified Euler constant. -/
theorem euler_log_moment_tail_zero :
    Tendsto (fun z : ℝ => ∫ t : ℝ in Ioi z, log t * exp (-t))
      (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have h := euler_log_moment_integrable.continuousOn_Ici_primitive_Ioi 0 (by simp)
  change Tendsto _ _ (𝓝 (∫ t : ℝ in Ioi 0, log t * exp (-t))) at h
  rw [euler_log_moment] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The singular logarithm is canceled by the first-order exponential zero. -/
theorem euler_small_boundary :
    Tendsto (fun z : ℝ => (1 - exp (-z)) * log z) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun z : ℝ => 1 - exp (-z)) 1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).neg.exp).const_sub 1)
  have hs : Tendsto (fun z : ℝ => (1 - exp (-z)) / z) (𝓝[>] 0) (𝓝 1) := by
    have h := hd.tendsto_slope_zero.mono_left
      (nhdsWithin_mono (0 : ℝ) (show Ioi 0 ⊆ {0}ᶜ by intro z hz; simpa using ne_of_gt hz))
    simpa only [zero_add, neg_zero, exp_zero, sub_self, sub_zero,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  have hl : Tendsto (fun z : ℝ => z * log z) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_mul_log.continuousAt (x := 0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := hs.mul hl
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change 0 < z at hz
  field_simp

/-- The actual exponential integral has the Euler logarithmic constant. -/
theorem buchstabE1_add_log_tendsto :
    Tendsto (fun z : ℝ => buchstabE1 z + log z) (𝓝[>] 0)
      (𝓝 (-eulerMascheroniConstant)) := by
  have h := euler_small_boundary.add euler_log_moment_tail_zero
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (buchstabE1_log_identity hz).symm

/-- Euler normalization before identifying the Buchstab transform with this solution. -/
theorem buchstabE1_scaled_exp_tendsto :
    Tendsto (fun z : ℝ => z * exp (buchstabE1 z)) (𝓝[>] 0)
      (𝓝 (exp (-eulerMascheroniConstant))) := by
  have h := (continuous_exp.tendsto (-eulerMascheroniConstant)).comp buchstabE1_add_log_tendsto
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  change exp (buchstabE1 z + log z) = z * exp (buchstabE1 z)
  rw [exp_add, exp_log hz, mul_comm]

end Wu2008DoubleSieve.SecondFunctionalJointTail
