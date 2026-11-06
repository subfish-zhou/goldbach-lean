import MathlibNt.Wu2008DoubleSieve.CoefficientRecurrence
import MathlibNt.Wu2008DoubleSieve.ReboxingEffectiveTransport

/-!
# The actual finite-threshold effective integral and its inner limit

This is the coefficient calculation following Wu04 (3.20), retaining the
required denominator. The threshold limit is taken at fixed depth.
-/

namespace Wu2008DoubleSieve

open Filter Real MeasureTheory
open scoped Topology Interval

theorem wuEffectiveCoefficient_integral_eventually (upper : Bool) (k : ℕ) (hk : 1 ≤ k)
    {δ s t : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    ∀ᶠ N0 : ℕ in atTop,
      (∫ u in (s - 1)..(t - 1), wuEffectiveCoefficient upper k δ N0 u / u) =
        if upper then
          wuLowerCoefficient t - wuLowerCoefficient s -
            ∫ u in (s - 1)..(t - 1), wuImprovementAt true k δ u N0 / u
        else
          wuUpperCoefficient t - wuUpperCoefficient s +
            ∫ u in (s - 1)..(t - 1), wuImprovementAt false k δ u N0 / u := by
  have h1 : 1 ≤ s - 1 := by linarith
  have hst' : s - 1 ≤ t - 1 := by linarith
  have ht' : t - 1 ≤ 10 := by linarith
  filter_upwards [wuImprovementAt_eventually_intervalIntegrable upper k hk hδ hδhi
    h1 hst' ht'] with N0 hi
  cases upper
  · simp only [wuEffectiveCoefficient, Bool.false_eq_true, if_false, add_div]
    rw [intervalIntegral.integral_add
      (wuLowerCoefficient_div_intervalIntegrable (by linarith) hst') hi,
      ← wuUpperCoefficient_sub_eq_integral hs hst]
  · simp only [wuEffectiveCoefficient, if_true, sub_div]
    rw [intervalIntegral.integral_sub
      (wuUpperCoefficient_div_intervalIntegrable (by linarith) hst') hi,
      ← wuLowerCoefficient_sub_eq_integral hs hst]


end Wu2008DoubleSieve
