import MathlibNt.SieveTheory.LiLiuGoldbachS4FiniteError

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε Z : ℝ,
      1 ≤ Z → Z ≤ (N : ℝ) ^ (1 / 4 : ℝ) →
      400 * (goldbachBadCount (goldbachDifferenceCarrier N ε) N : ℝ) +
        400 * (Nat.floor Z : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ)^2) := by
  obtain ⟨N₀, hN₀, hh⟩ := goldbachS4_finiteLoss_normalized δ hδ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ε Z hZ hZu
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq : (N : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  exact hh N hN ε Z (by linarith) (hZu.trans hq)

#check goldbachS4_finiteLoss_le_sqrt
#print axioms goldbachS4_finiteLoss_le_sqrt
#check goldbachS4_finiteLoss_normalized
#print axioms goldbachS4_finiteLoss_normalized

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig