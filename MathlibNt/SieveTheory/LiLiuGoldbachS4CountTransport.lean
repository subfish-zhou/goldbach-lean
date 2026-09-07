import MathlibNt.SieveTheory.LiLiuGoldbachS4SwitchedCarrier
import MathlibNt.SieveTheory.LiLiuGoldbachS4FiniteError

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual S4 is transported to the labelled one-prefix switched count,
with the bad-companion and small-output losses both absorbed. This leaves
the switched sifted count itself to be estimated analytically. -/
theorem goldbachS4_le_sifted_B8Plus_with_paid_finite_error
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Z : ℝ,
      1 ≤ Z → Z ≤ Real.sqrt (N : ℝ) →
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
        ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) +
          δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨Nc, _hNc, hc⟩ := goldbachS4_eventually_le_sifted_B8Plus ε hε hεu
  obtain ⟨Ne, hNe, he⟩ := goldbachS4_finiteLoss_normalized δ hδ
  refine ⟨max Nc Ne, hNe.trans (le_max_right _ _), ?_⟩
  intro N hN Z hZ hZu
  have hcN := hc N ((le_max_left _ _).trans hN) Z hZ
  have hcR :
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ (3 / 11 : ℝ)) : ℝ) ≤
        ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) +
          400 * (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) +
          400 * (Nat.floor Z : ℝ) := by exact_mod_cast hcN
  have heN := he N ((le_max_right _ _).trans hN) ε Z (by linarith) hZu
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig