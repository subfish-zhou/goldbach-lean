import MathlibNt.Wu2008DoubleSieve.Omega2RawNormalized
import MathlibNt.Wu2008DoubleSieve.Omega2CanonicalIntegral

/-!
# The actual lower Omega2 estimate, Wu04 (5.2)

Both the raw fixed-cutoff comparison and the normalized prime integral
are consumed with one epsilon budget. The negative sign in the first
weighted inequality therefore receives a lower, not an upper, estimate.
-/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

theorem wu04_52 (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      ((∫ u in (1 - 1 / s)..(1 - 1 / t),
        (wuLowerCoefficient (t * u) + wuImprovementAt false (k + 1) δ (t * u) N0) /
          (u * (1 - u))) - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  obtain ⟨T1, hT14, hT1⟩ := wuOmega2Sum_lower_normalized_prime k hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := omega2_effective_prime_integral_relative false k hδ
    (show δ < 1 / 2 by linarith) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hst ht ht5
  have hr := hT1 N0 ((le_max_left _ _).trans hN0) N hN he i Δ V hb s t hs hst ht ht5
  have hi := (abs_le.mp (hT2 N0 ((le_max_right _ _).trans hN0) N hN i Δ V hb
    s t hs hst ht ht5)).1
  simp only [wuEffectiveCoefficient, Bool.false_eq_true, if_false] at hr hi
  nlinarith


end Wu2008DoubleSieve
