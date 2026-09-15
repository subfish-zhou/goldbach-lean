import MathlibNt.Wu2008DoubleSieve.NinthMainMassIntegral
import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedGeometry

/-!
# Exact classical seventh and eighth integrals

The kernel is the accepted global-scale reciprocal kernel, with no squared
last denominator. These are analytic identities, not upper bounds for the
physical counts. The generic slice includes the collapsed upper endpoint.
-/
namespace Wu2008DoubleSieve.SeventhEighth
open Set Real MeasureTheory
open scoped Interval

noncomputable def classicalKernel (t v : ℝ) : ℝ := 1 / (t * v * (1 - t - v))
noncomputable def J7 : ℝ :=
  ∫ t in sigma..(1 / 3), log ((1 - 2 * t) / t) / (t * (1 - t))
noncomputable def J8 : ℝ :=
  ∫ t in alpha..(1 / 3), log (2 - 3 * t) / (t * (1 - t))

theorem classical_parameters :
    0 < alpha ∧ alpha < sigma ∧ sigma < 1 / 3 := by
  norm_num [alpha, sigma]

/-- A parameterized FTC, proved on the actual positive slice. -/
theorem classical_slice_integral {t l : ℝ}
    (ht : 0 < t) (hl : 0 < l) (hlo : l ≤ (1 - t) / 2) :
    (∫ v in l..((1 - t) / 2), classicalKernel t v) =
      log ((1 - t - l) / l) / (t * (1 - t)) := by
  have ht1 : 0 < 1 - t := by linarith
  have hdl : 0 < 1 - t - l := by linarith
  have hd : ∀ v ∈ uIcc l ((1 - t) / 2),
      HasDerivAt (fun v => (log v - log (1 - t - v)) / (1 - t))
        (1 / (1 - t - v) / v) v := by
    intro v hv
    rw [uIcc_of_le hlo] at hv
    have hv0 : 0 < v := hl.trans_le hv.1
    have hvd : 0 < 1 - t - v := by linarith [hv.2]
    have h := ((hasDerivAt_log hv0.ne').sub
      (((hasDerivAt_const v (1 - t)).sub (hasDerivAt_id v)).log hvd.ne')).div_const (1 - t)
    dsimp only [Pi.sub_apply, id_eq] at h
    convert h using 1 <;> first | rfl | (field_simp; ring)
  have hc : ContinuousOn (fun v => 1 / (1 - t - v) / v)
      (Icc l ((1 - t) / 2)) := by
    apply ContinuousOn.div
    · apply continuousOn_const.div
      · fun_prop
      · intro v hv
        have : 0 < 1 - t - v := by linarith [hv.2]
        exact this.ne'
    · exact continuousOn_id
    · intro v hv
      exact (hl.trans_le hv.1).ne'
  have hi : IntervalIntegrable (fun v => 1 / (1 - t - v) / v) volume
      l ((1 - t) / 2) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hlo] using hc
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have heq : (fun v => classicalKernel t v) =
      (fun v => (1 / (1 - t - v) / v) / t) := by
    funext v
    unfold classicalKernel
    simp only [div_div]
    congr 1
    ring
  rw [heq, intervalIntegral.integral_div, he]
  rw [show 1 - t - (1 - t) / 2 = (1 - t) / 2 by ring,
    sub_self, zero_div, zero_sub, log_div hdl.ne' hl.ne']
  field_simp
  ring

theorem seventh_slice {t : ℝ} (ht : t ∈ Icc sigma (1 / 3 : ℝ)) :
    (∫ v in t..((1 - t) / 2), classicalKernel t v) =
      log ((1 - 2 * t) / t) / (t * (1 - t)) := by
  have ht0 : 0 < t := (classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1
  simpa only [show 1 - t - t = 1 - 2 * t by ring] using
    classical_slice_integral ht0 ht0 (by linarith [ht.2])

theorem eighth_slice {t : ℝ} (ht : t ∈ Icc alpha (1 / 3 : ℝ)) :
    (∫ v in (1 / 3 : ℝ)..((1 - t) / 2), classicalKernel t v) =
      log (2 - 3 * t) / (t * (1 - t)) := by
  have ht0 : 0 < t := classical_parameters.1.trans_le ht.1
  simpa only [show (1 - t - (1 / 3 : ℝ)) / (1 / 3) = 2 - 3 * t by ring] using
    classical_slice_integral ht0 (by norm_num : (0 : ℝ) < 1 / 3) (by linarith [ht.2])

theorem J7_eq_triangle_integral :
    J7 = ∫ t in sigma..(1 / 3),
      ∫ v in t..((1 - t) / 2), classicalKernel t v := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le classical_parameters.2.2.le] at ht
  exact (seventh_slice ht).symm

theorem J8_eq_triangle_integral :
    J8 = ∫ t in alpha..(1 / 3),
      ∫ v in (1 / 3 : ℝ)..((1 - t) / 2), classicalKernel t v := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (classical_parameters.2.1.le.trans classical_parameters.2.2.le)] at ht
  exact (eighth_slice ht).symm

theorem seventh_integrand_continuous :
    ContinuousOn (fun t => log ((1 - 2 * t) / t) / (t * (1 - t)))
      (Icc sigma (1 / 3 : ℝ)) := by
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).div
        continuousOn_id (fun t ht =>
          ((classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1).ne')
    · intro t ht
      have ht0 : 0 < t := (classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1
      exact (div_pos (by linarith [ht.2] : 0 < 1 - 2 * t) ht0).ne'
  · fun_prop
  · intro t ht
    exact mul_ne_zero
      ((classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1).ne'
      (by linarith [ht.2])

theorem eighth_integrand_continuous :
    ContinuousOn (fun t => log (2 - 3 * t) / (t * (1 - t)))
      (Icc alpha (1 / 3 : ℝ)) := by
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · fun_prop
    · intro t ht
      have : 0 < 2 - 3 * t := by linarith [ht.2]
      exact this.ne'
  · fun_prop
  · intro t ht
    exact mul_ne_zero (classical_parameters.1.trans_le ht.1).ne' (by linarith [ht.2])

theorem J7_integrable :
    IntervalIntegrable (fun t => log ((1 - 2 * t) / t) / (t * (1 - t)))
      volume sigma (1 / 3) := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le classical_parameters.2.2.le] using seventh_integrand_continuous

theorem J8_integrable :
    IntervalIntegrable (fun t => log (2 - 3 * t) / (t * (1 - t)))
      volume alpha (1 / 3) := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (classical_parameters.2.1.le.trans classical_parameters.2.2.le)] using
    eighth_integrand_continuous

theorem J7_nonneg : 0 ≤ J7 := by
  apply intervalIntegral.integral_nonneg classical_parameters.2.2.le
  intro t ht
  have ht0 : 0 < t := (classical_parameters.1.trans classical_parameters.2.1).trans_le ht.1
  have hr : 1 ≤ (1 - 2 * t) / t := (le_div_iff₀ ht0).mpr (by linarith [ht.2])
  exact div_nonneg (log_nonneg hr) (mul_nonneg ht0.le (by linarith [ht.2]))

theorem J8_nonneg : 0 ≤ J8 := by
  apply intervalIntegral.integral_nonneg
    (classical_parameters.2.1.le.trans classical_parameters.2.2.le)
  intro t ht
  have ht0 : 0 < t := classical_parameters.1.trans_le ht.1
  exact div_nonneg (log_nonneg (by linarith [ht.2] : 1 ≤ 2 - 3 * t))
    (mul_nonneg ht0.le (by linarith [ht.2]))

end Wu2008DoubleSieve.SeventhEighth
