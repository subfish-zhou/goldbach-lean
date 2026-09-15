import E07FifthSourceBranches

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open Wu08OriginalFirstSteps
open scoped Interval
noncomputable section

def recurrenceIntegrand (s u : ℝ) : ℝ :=
  log (u-1)/u*(log (s-1)-log (u+1))

theorem B_derivative (s : ℝ) : HasDerivAt B (k (s-1)) s := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (k_continuous.intervalIntegrable (μ := volume) 2 (s-1))
    k_continuous.stronglyMeasurable.stronglyMeasurableAtFilter k_continuous.continuousAt
  convert hi.comp s ((hasDerivAt_id s).sub_const 1) using 1 <;>
    first | rfl | simp

theorem recurrence_one_dimensional {s : ℝ} (hs : 4 ≤ s) :
    C s = ∫ u in (2 : ℝ)..(s-2), recurrenceIntegrand s u := by
  have h3 : (3 : ℝ) ≤ s-1 := by linarith
  have h2 : (2 : ℝ) ≤ s-2 := by linarith
  have hn (t : ℝ) (ht : t ∈ uIcc 3 (s-1)) : t ≠ 0 := by
    rw [uIcc_of_le h3] at ht
    linarith [ht.1]
  have hi1 : IntervalIntegrable (fun t => k (t-1)) volume 3 (s-1) :=
    (k_continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 3 (s-1) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.inv₀ hn
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => B_derivative t) (fun t ht => hasDerivAt_log (hn t ht)) hi1 hi2
  have heC : (∫ t in (3 : ℝ)..(s-1), B t*t⁻¹) = C s := by
    unfold C
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le h3] at ht
    change B t*t⁻¹ = B t/max 1 t
    rw [max_eq_right (by linarith [ht.1]), div_eq_mul_inv]
  have heB : B 3 = 0 := by norm_num [B]
  rw [heC, heB, zero_mul, sub_zero] at hparts
  have hshift : (∫ u in (2 : ℝ)..(s-2), k u*log (u+1)) =
      ∫ t in (3 : ℝ)..(s-1), k (t-1)*log t := by
    have h := intervalIntegral.integral_comp_add_right
      (fun t => k (t-1)*log t) 1 (a := 2) (b := s-2)
    simpa only [add_sub_cancel_right, show (2 : ℝ)+1=3 by norm_num,
      show s-2+1=s-1 by ring] using h
  have hi3 : IntervalIntegrable (fun u => k u*log (u+1)) volume 2 (s-2) := by
    apply ContinuousOn.intervalIntegrable
    apply k_continuous.continuousOn.mul
    exact (continuousOn_id.add continuousOn_const).log (by
      intro u hu
      rw [uIcc_of_le h2] at hu
      change u+1 ≠ 0
      linarith [hu.1])
  have hi4 : IntervalIntegrable (fun u => k u*log (s-1)) volume 2 (s-2) :=
    (k_continuous.intervalIntegrable _ _).mul_const _
  have he : (∫ u in (2 : ℝ)..(s-2), recurrenceIntegrand s u) =
      B (s-1)*log (s-1)-(∫ t in (3 : ℝ)..(s-1), k (t-1)*log t) := by
    calc
      _ = ∫ u in (2 : ℝ)..(s-2), k u*log (s-1)-k u*log (u+1) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le h2] at hu
        change recurrenceIntegrand s u = _
        rw [k_literal hu.1]
        unfold recurrenceIntegrand
        ring
      _ = B (s-1)*log (s-1)-(∫ t in (3 : ℝ)..(s-1), k (t-1)*log t) := by
        rw [intervalIntegral.integral_sub hi4 hi3, intervalIntegral.integral_mul_const, hshift]
        unfold B
        rw [show s-1-1=s-2 by ring]
  linarith only [hparts, he]

theorem coefficient_single_recurrence {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    wuLowerCoefficient s =
      log (s-1)+∫ u in (2 : ℝ)..(s-2), recurrenceIntegrand s u := by
  rw [lower_middle hs hs6, recurrence_one_dimensional hs]

theorem recurrence_integrand_nonneg {s u : ℝ} (hs : 4 ≤ s)
    (hu : u ∈ Icc 2 (s-2)) : 0 ≤ recurrenceIntegrand s u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hlog : log (u+1) ≤ log (s-1) :=
    log_le_log (by linarith [hu.1]) (by linarith [hu.2])
  unfold recurrenceIntegrand
  exact mul_nonneg (div_nonneg (log_nonneg (by linarith [hu.1])) hu0.le)
    (sub_nonneg.mpr hlog)

end
end WuTarget.Wu08FifthSource
