import MathlibNt.SieveTheory.LiLiuPrereqWFExternalSieve
import MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedRemainder

/-! The actual progression density, in the standard multiplicative omega interface.
All identities retain the given density at every natural number, including zero.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open scoped Classical

/-- The actual sieve weight, not a squarefree surrogate. -/
noncomputable def progressionOmega (v : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * progressionDensity v n, by simp⟩

@[simp] theorem progressionOmega_apply (v n : ℕ) :
    progressionOmega v n = (n : ℝ) * progressionDensity v n := rfl

/-- Multiplicativity is proved directly from coprimality and Euler's totient. -/
theorem progressionOmega_isMultiplicative (v : ℕ) :
    (progressionOmega v).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [progressionOmega, progressionDensity]
  · intro m n hmn
    change ((m * n : ℕ) : ℝ) *
        (if (m * n).Coprime v then ((m * n).totient : ℝ)⁻¹ else 0) =
      ((m : ℝ) * (if m.Coprime v then (m.totient : ℝ)⁻¹ else 0)) *
      ((n : ℝ) * (if n.Coprime v then (n.totient : ℝ)⁻¹ else 0))
    simp only [Nat.totient_mul hmn, Nat.coprime_mul_iff_left, Nat.cast_mul]
    split_ifs <;> simp_all [mul_inv_rev]
    ring

@[simp] theorem primeDensity_progressionOmega_apply (v n : ℕ) :
    primeDensity (progressionOmega v) n = progressionDensity v n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [primeDensity_apply, progressionOmega_apply]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast hn)

/-- Equality as arithmetic functions, with no nonzero or squarefree restriction. -/
@[simp] theorem primeDensity_progressionOmega (v : ℕ) :
    primeDensity (progressionOmega v) = progressionDensity v := by
  ext n
  exact primeDensity_progressionOmega_apply v n

theorem progressionDensity_prime (v : ℕ) {p : ℕ} (hp : p.Prime) :
    progressionDensity v p = if p.Coprime v then 1 / ((p : ℝ) - 1) else 0 := by
  change (if p.Coprime v then (p.totient : ℝ)⁻¹ else 0) = _
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  simp [one_div]

theorem progressionDensity_prime_nonneg_lt_one (v : ℕ) {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    0 ≤ progressionDensity v p ∧ progressionDensity v p < 1 := by
  rw [progressionDensity_prime v hp]
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hp2
  split_ifs
  · constructor
    · exact div_nonneg (by norm_num) (by linarith)
    · apply (div_lt_one (by linarith : 0 < (p : ℝ) - 1)).mpr
      linarith
  · norm_num

/-- Prime hypotheses in exactly the quotient form expected by ExternalSieve. -/
theorem progressionOmega_prime_nonneg_lt_one (v : ℕ) {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    0 ≤ progressionOmega v p / (p : ℝ) ∧
      progressionOmega v p / (p : ℝ) < 1 := by
  change 0 ≤ primeDensity (progressionOmega v) p ∧
    primeDensity (progressionOmega v) p < 1
  simpa only [primeDensity_progressionOmega_apply] using
    progressionDensity_prime_nonneg_lt_one v hp hp2

/-- The genuine Euler product, on any finite set of primes. -/
theorem progressionOmega_eulerProduct (v : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - progressionOmega v p / (p : ℝ))) =
      ∏ p ∈ P, (1 - if p.Coprime v then 1 / ((p : ℝ) - 1) else 0) := by
  apply prod_congr rfl
  intro p hp
  rw [← primeDensity_apply, primeDensity_progressionOmega_apply,
    progressionDensity_prime v (hP p hp)]

/-- Primes dividing the progression parameter contribute the exact unit factor. -/
theorem progressionOmega_eulerProduct_filter (v : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, (1 - progressionOmega v p / (p : ℝ))) =
      ∏ p ∈ P.filter (fun p => p.Coprime v), (1 - 1 / ((p : ℝ) - 1)) := by
  rw [progressionOmega_eulerProduct v P hP, prod_filter]
  apply prod_congr rfl
  intro p _
  split_ifs <;> simp

end MathlibNt.SieveTheory.LiLiuPrereqWF
