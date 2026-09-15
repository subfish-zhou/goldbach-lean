import Mathlib.NumberTheory.AlmostPrime
import Mathlib.Tactic.Linarith

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
  refine ⟨hp.two_le, ?_⟩
  exact hp.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2)

/-- A product of two primes has at most two prime factors; equal factors are allowed. -/
theorem mul_prime_semiprime {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    Semiprime (p₁ * p₂) := by
  refine ⟨?_, ?_⟩
  · have h1 : (2 : ℕ) ≤ p₁ := hp₁.two_le
    have h2 : (2 : ℕ) ≤ p₂ := hp₂.two_le
    nlinarith
  · exact hp₁.mul_isAlmostPrime_two hp₂ |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-- The internal predicate is exactly a prime or a product of two primes. -/
theorem semiprime_iff :
    Semiprime n ↔ n.Prime ∨ ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ n = p₁ * p₂ := by
  constructor
  · -- Mathlib definition → constructive definition
    intro h
    obtain ⟨hn2, hn⟩ := h
    obtain ⟨hn0, hΩ⟩ := hn
    -- Since n ≥ 2, n ≠ 1 and there is a prime factor p ∣ n.
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hn1
    -- n = p * m
    obtain ⟨m, hm⟩ := exists_eq_mul_right_of_dvd hp_dvd
    -- p ≠ 0 (since p is prime), and m ≠ 0 (since n ≠ 0 and n = p * m).
    have hp0 : p ≠ 0 := hp.ne_zero
    have hm0 : m ≠ 0 := by
      intro heq; rw [heq, mul_zero] at hm; omega
    -- Ω(n) = Ω(p * m) = Ω(p) + Ω(m) = 1 + Ω(m)
    have hΩn : Ω n = 1 + Ω m := by
      rw [hm, ArithmeticFunction.cardFactors_mul hp0 hm0,
        ArithmeticFunction.cardFactors_apply_prime hp]
    -- Ω(m) ≤ 1
    have hΩm_le : Ω m ≤ 1 := by omega
    -- Split into cases according to Ω(m).
    by_cases h0 : Ω m = 0
    · -- Ω(m) = 0 → m = 1 → n = p → n is prime.
      left
      have hm1 : m = 1 := by
        rcases ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp h0 with h | h
        · exact absurd h hm0
        · exact h
      rw [hm, hm1, mul_one]
      exact hp
    · -- Ω(m) = 1 → m is prime → n = p * m.
      right
      have hm_prime : m.Prime :=
        ArithmeticFunction.cardFactors_eq_one_iff_prime.mp (by omega)
      exact ⟨p, m, hp, hm_prime, hm⟩
  · -- Constructive definition → Mathlib definition
    rintro (hn | ⟨p₁, p₂, hp₁, hp₂, hn⟩)
    · -- n is prime: Ω(n) = 1 ≤ 2 and n ≥ 2.
      refine ⟨hn.two_le, ?_⟩
      exact hn.isAlmostPrime_one.isAtMost (by decide : (1 : ℕ) ≤ 2)
    · -- n = p₁ * p₂: Ω(n) = 2 ≤ 2, n ≥ 4 ≥ 2
      subst hn
      refine ⟨?_, ?_⟩
      · nlinarith [hp₁.two_le, hp₂.two_le]
      · exact hp₁.mul_isAlmostPrime_two hp₂ |>.isAtMost (by decide : (2 : ℕ) ≤ 2)

/-- The internal predicate excludes zero and one. -/
theorem semiprime_ge_two {n : ℕ} (h : Semiprime n) : n ≥ 2 := h.1

/-- Mathlib's exactly-two-factor predicate implies the at-most-two-factor predicate. -/
theorem isSemiprime_implies_semiprime {n : ℕ} (h : n.IsSemiprime) : Semiprime n := by
  have hΩ : Ω n = 2 := h.2
  have hn2 : 2 ≤ n := by
    have hΩpos : 0 < Ω n := hΩ ▸ (by decide : (0 : ℕ) < 2)
    have h1lt : 1 < n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp hΩpos
    omega
  refine ⟨hn2, ?_⟩
  exact h.isAtMost (by decide : (2 : ℕ) ≤ 2)

end MathlibNt.ChensTheorem
