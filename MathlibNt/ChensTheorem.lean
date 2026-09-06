import Mathlib.NumberTheory.AlmostPrime

/-!
# Prime-plus-at-most-two-primes representation vocabulary

This foundational module defines the second-summand predicate and proves its
literal characterization. It does not import any sieve implementation.
The unconditional theorem is exposed by `Goldbach`.

The retained internal name `Semiprime` means *at most* two prime factors here;
Mathlib's `Nat.IsSemiprime` means exactly two. The public theorem avoids that
terminological ambiguity by stating the disjunction explicitly.
-/

namespace MathlibNt.ChensTheorem

open scoped ArithmeticFunction.Omega

/-- An integer at least two with at most two prime factors, counted with multiplicity. -/
def Semiprime (n : ℕ) : Prop :=
  n ≥ 2 ∧ Nat.IsAtMostAlmostPrime 2 n

/-- A prime has at most two prime factors. -/
theorem prime_semiprime {p : ℕ} (hp : p.Prime) : Semiprime p := by
  exact ⟨hp.two_le, hp.isAlmostPrime_one.isAtMost (by decide)⟩

/-- A product of two primes has at most two prime factors; equal factors are allowed. -/
theorem mul_prime_semiprime {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    Semiprime (p₁ * p₂) := by
  exact ⟨hp₁.two_le.trans (Nat.le_mul_of_pos_right _ hp₂.pos),
    (hp₁.mul_isAlmostPrime_two hp₂).isAtMost le_rfl⟩

/-- The internal predicate is exactly a prime or a product of two primes. -/
theorem semiprime_iff :
    Semiprime n ↔ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ n = p₁ * p₂ := by
  constructor
  · rintro ⟨hn2, hn0, hΩ⟩
    -- Remove one prime factor. The remaining factor has at most one prime factor.
    obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨m, hm⟩ := exists_eq_mul_right_of_dvd hp_dvd
    have hm0 : m ≠ 0 := by
      intro hm_zero
      simp [hm_zero] at hm
      exact hn0 hm
    have hΩn : Ω n = 1 + Ω m := by
      rw [hm, ArithmeticFunction.cardFactors_mul hp.ne_zero hm0,
        ArithmeticFunction.cardFactors_apply_prime hp]
    -- A unit cofactor gives a prime; every other cofactor must itself be prime.
    by_cases hm1 : m = 1
    · exact Or.inl (by simpa [hm, hm1] using hp)
    · have hΩm_pos : 0 < Ω m :=
        ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
      have hm_prime : m.Prime :=
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
      exact Or.inr ⟨p, m, hp, hm_prime, hm⟩
  · rintro (hn | ⟨p₁, p₂, hp₁, hp₂, rfl⟩)
    · exact prime_semiprime hn
    · exact mul_prime_semiprime hp₁ hp₂

/-- The internal predicate excludes zero and one. -/
theorem semiprime_ge_two {n : ℕ} (h : Semiprime n) : n ≥ 2 := h.1

/-- Mathlib's exactly-two-factor predicate implies the at-most-two-factor predicate. -/
theorem isSemiprime_implies_semiprime {n : ℕ} (h : n.IsSemiprime) : Semiprime n := by
  have hΩ : Ω n = 2 := h.2
  have hn2 : 2 ≤ n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp (by omega : 0 < Ω n)
  exact ⟨hn2, h.isAtMost le_rfl⟩

end MathlibNt.ChensTheorem
