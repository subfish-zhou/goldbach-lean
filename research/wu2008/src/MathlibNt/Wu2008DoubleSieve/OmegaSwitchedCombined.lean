import MathlibNt.Wu2008DoubleSieve.OmegaCombined
import MathlibNt.Wu2008DoubleSieve.Omega3Relative

/-! # The actual first weighted comparison after switching -/

namespace Wu2008DoubleSieve

open Real
open scoped Interval

/-- The remaining positive term is the actual strengthened switched sieve,
not an arbitrary error or an assumed switching bound. -/
theorem wu04_first_weighted_switched (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ 3 → 3 ≤ t → t ≤ 5 → 2 ≤ t - t / s →
        let W := convolutionWuWindows N Δ V
        2 * wuBoxPhi N δ W s ≤
          (2 * (wuUpperCoefficient t - wuImprovementAt true k δ t N0) -
            (∫ u in (1 - 1 / s)..(1 - 1 / t),
              (log (t * u - 1) + wuImprovementAt false (k + 1) δ (t * u) N0) /
                (u * (1 - u))) + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W +
          omega3SwitchedSiftedCount N δ s t (sqrt ((N : ℝ) ^ (1 / 2 - δ))) W := by
  obtain ⟨T1, hT14, hT1⟩ := wu04_first_weighted_omega12 k hk hδ hδhi (half_pos hε)
  obtain ⟨T2, _, hT2⟩ := wu04_54 k hδ (show δ < 1 / 2 by linarith) (half_pos hε)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N0 hN0 N hN he i Δ V hb s t hs hs3 ht ht5 hratio
  have h1 := hT1 N0 ((le_max_left _ _).trans hN0) N hN he
    i Δ V hb s t hs hs3 ht ht5 hratio
  have h2 := hT2 N0 ((le_max_right _ _).trans hN0) N hN he
    i Δ V hb s t hs (by linarith) (by linarith)
  dsimp only at h1 ⊢
  nlinarith

end Wu2008DoubleSieve
