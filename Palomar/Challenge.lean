module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Chen and Li–Liu representation theorems

Chen's theorem states that every sufficiently large even natural number is a
prime plus a prime or a product of two primes. The two factors may coincide.

The Li–Liu refinement controls the relative sizes of the two factors. Its exact
natural-power condition is `r ^ 10 ≤ q ^ 9`, equivalent here to `r ≤ q ^ (9/10)`.
The case `r = 1` includes a sum of two primes. Each theorem chooses a threshold
before quantifying over all subsequent even natural numbers.

This independent specification uses Mathlib declarations. Deliberate proof holes
identify the statements that Comparator must obtain from `Palomar.Solution`.
-/

public section

namespace GoldbachPalomar

/-- Chen's qualitative prime-plus-at-most-two-primes theorem. -/
theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧
        (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q := by
  sorry

/-- Li–Liu's refinement, with an exact natural-power comparison. -/
theorem one_plus_one_nine :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ r ^ 10 ≤ q ^ 9 := by
  sorry

/-- The same Li–Liu refinement with the paper's real exponent. -/
theorem one_plus_one_nine_real :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ ((19 / 10 : ℝ) - 1) := by
  sorry

end GoldbachPalomar
