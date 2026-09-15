import MathlibNt.Wu2008DoubleSieve.Omega2PrimeIntegral

/-!
# Integrability of the literal signed Omega2 main term

Wu04 (5.2) uses a+h, which can be negative at finite threshold.
Monotonicity provides integrability without assigning continuity to h.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory Filter
open scoped Interval Topology

theorem omega2_integral_domain {s t u : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5)
    (hu : u ∈ uIcc (1 - 1 / s) (1 - 1 / t)) :
    1 / 2 ≤ u ∧ u ≤ 4 / 5 ∧ t * u ∈ Icc (1 : ℝ) 10 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hab : 1 - 1 / s ≤ 1 - 1 / t :=
    sub_le_sub_left (one_div_le_one_div_of_le hs0 hst) 1
  rw [uIcc_of_le hab] at hu
  have hsl : 1 / s ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs
  have htr : 1 / 5 ≤ 1 / t := one_div_le_one_div_of_le ht0 ht5
  have hlo : 1 / 2 ≤ u := by linarith [hu.1]
  have hhi : u ≤ 4 / 5 := by linarith [hu.2]
  refine ⟨hlo, hhi, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hlo ht0.le]
  · nlinarith [mul_le_mul_of_nonneg_left hhi ht0.le]

theorem omega2_integral_intervalIntegrable {f : ℝ → ℝ} {s t : ℝ}
    (hf : MonotoneOn f (Icc 1 10))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    IntervalIntegrable (fun u => f (t * u) / (u * (1 - u))) volume
      (1 - 1 / s) (1 - 1 / t) := by
  have hm : MonotoneOn (fun u => f (t * u)) (uIcc (1 - 1 / s) (1 - 1 / t)) := by
    intro u hu v hv huv
    exact hf (omega2_integral_domain hs hst ht ht5 hu).2.2
      (omega2_integral_domain hs hst ht ht5 hv).2.2
      (mul_le_mul_of_nonneg_left huv (by linarith))
  have hc : ContinuousOn (fun u : ℝ => (u * (1 - u))⁻¹)
      (uIcc (1 - 1 / s) (1 - 1 / t)) := by
    apply (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).inv₀
    intro u hu
    have h := omega2_integral_domain hs hst ht ht5 hu
    exact mul_ne_zero (by change u ≠ 0; linarith [h.1])
      (by change 1 - u ≠ 0; linarith [h.2.1])
  simpa only [div_eq_mul_inv] using hm.intervalIntegrable.mul_continuousOn hc

theorem omega2_effective_integral_eventually_integrable (upper : Bool) (k : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop, ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      IntervalIntegrable (fun u =>
        wuEffectiveCoefficient upper (k + 1) δ N0 (t * u) / (u * (1 - u)))
        volume (1 - 1 / s) (1 - 1 / t) := by
  filter_upwards [wu_effective_threshold_uniform_monotone upper (k + 1) (by omega)
    hδ hδhi] with N0 hN0
  intro s t hs hst ht ht5
  exact omega2_integral_intervalIntegrable hN0 hs hst ht ht5

end Wu2008DoubleSieve
