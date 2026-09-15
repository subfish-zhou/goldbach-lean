import MathlibNt.Wu2008DoubleSieve.Omega2EffectiveIntegral

/-!
# The canonical lower branch in Wu04 (5.2)

The extra source condition t-t/s >= 2 places every lower coefficient
in the proved logarithmic branch [2,4]. This is separate from the
broader domain of the prime integral and does not estimate Omega3.
-/

namespace Wu2008DoubleSieve

open Set Real
open scoped Interval

theorem omega2_canonical_parameter_mem {s t u : ℝ}
    (hs : 2 ≤ s) (hst : s ≤ t) (ht5 : t ≤ 5) (hratio : 2 ≤ t - t / s)
    (hu : u ∈ uIcc (1 - 1 / s) (1 - 1 / t)) :
    t * u ∈ Icc (2 : ℝ) 4 := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hab : 1 - 1 / s ≤ 1 - 1 / t :=
    sub_le_sub_left (one_div_le_one_div_of_le hs0 hst) 1
  rw [uIcc_of_le hab] at hu
  have hl := mul_le_mul_of_nonneg_left hu.1 ht0.le
  have hh := mul_le_mul_of_nonneg_left hu.2 ht0.le
  have hleft : t * (1 - 1 / s) = t - t / s := by ring
  have hright : t * (1 - 1 / t) = t - 1 := by field_simp
  rw [hleft] at hl
  rw [hright] at hh
  exact ⟨hratio.trans hl, by linarith⟩

theorem omega2_effective_lower_integral_eq_log (k N0 : ℕ) (δ : ℝ)
    {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht5 : t ≤ 5)
    (hratio : 2 ≤ t - t / s) :
    (∫ u in (1 - 1 / s)..(1 - 1 / t),
      wuEffectiveCoefficient false (k + 1) δ N0 (t * u) / (u * (1 - u))) =
    ∫ u in (1 - 1 / s)..(1 - 1 / t),
      (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
        (u * (1 - u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  have h := omega2_canonical_parameter_mem hs hst ht5 hratio hu
  have ha : wuLowerCoefficient (t * u) = log (t * u - 1) :=
    jr1965f_normalized_firstInterval h.1 h.2
  simp only [wuEffectiveCoefficient, Bool.false_eq_true, if_false, ha]

end Wu2008DoubleSieve
