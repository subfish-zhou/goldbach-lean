import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorActualContract
import MathlibNt.SieveTheory.LiLiuGoldbachConditionalFinalAssembly

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Consume the new actual G11 producer in the existing signed ledger. Only
the independently owned literal remaining-count estimate is still a premise. -/
theorem goldbachD19_author_actual_lower_of_remaining (r : ℝ)
    (hRemaining : ∀ δ : ℝ, 0 < δ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
          ∃ Z : ℝ, 1 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
            (r-δ)*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤
              (goldbachWeightG11PaidBase N ε : ℝ)-(goldbachB9LowPositivePrefixSiftedCount N ε Z : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ (2/15 : ℝ) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ((r-(10191/100000 : ℝ)-(661251229/200000000 : ℝ)-δ)/4)*
            (SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) ≤ (D19 N : ℝ) :=
  goldbachD19_small_epsilon_lower_with_error_of_actual_estimates
    (10191/100000) r goldbachWeightG11_author_actual_small_epsilon hRemaining δ hδ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig