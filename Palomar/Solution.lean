module

public import Goldbach.All

/-! # Implementations of the independent Palomar representation statements -/

public section

namespace GoldbachPalomar

/-- The public Chen proof supplies the literal prime-factor alternatives. -/
theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ p q : ℕ, p.Prime ∧
        (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q :=
  Goldbach.chen_theorem

/-- The public Li–Liu proof supplies the exact natural-power condition. -/
theorem one_plus_one_nine :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ r ^ 10 ≤ q ^ 9 :=
  Goldbach.one_plus_one_nine

/-- The public real-power proof supplies the paper's exponent convention. -/
theorem one_plus_one_nine_real :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ ((19 / 10 : ℝ) - 1) :=
  Goldbach.one_plus_one_nine_real

end GoldbachPalomar
