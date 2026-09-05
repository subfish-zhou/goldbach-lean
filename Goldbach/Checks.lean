import Goldbach

/-! # Public theorem type and axiom checks -/

#print Goldbach.ChenTheorem
#check @Goldbach.chen_theorem
#check @Goldbach.representation_lower_bound
#print axioms Goldbach.chen_theorem
#print axioms Goldbach.representation_lower_bound
#print axioms MathlibNt.ChensTheorem.chens_theorem_unconditional
#print axioms MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional

/-- An expanded type check, with no project-specific predicate in its statement. -/
example : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p q : ℕ, p.Prime ∧
      (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q :=
  Goldbach.chen_theorem

/-- The original implementation must retain its unconditional qualitative type. -/
example : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
    ∃ p q : ℕ, p.Prime ∧ MathlibNt.ChensTheorem.Semiprime q ∧ N = p + q :=
  MathlibNt.ChensTheorem.chens_theorem_unconditional

/-- The public quantitative type fixes the coefficient, normalization, and actual count. -/
example : ∀ᶠ N : ℕ in Filter.atTop, Even N →
    (0.67 : ℝ) * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ) ≤
    ((MathlibNt.SieveTheory.SwitchingPrinciple.chenGoodRepresentations N).card : ℝ) :=
  Goldbach.representation_lower_bound

/-- The implementation endpoint is checked against the same independent explicit type. -/
example : ∀ᶠ N : ℕ in Filter.atTop, Even N →
    (0.67 : ℝ) * MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ) ≤
    ((MathlibNt.SieveTheory.SwitchingPrinciple.chenGoodRepresentations N).card : ℝ) :=
  MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional

/-- Repeated prime factors are admitted by the internal representation model. -/
example : MathlibNt.ChensTheorem.Semiprime 4 :=
  MathlibNt.ChensTheorem.mul_prime_semiprime Nat.prime_two Nat.prime_two

/-- Neither zero nor one is a valid second summand in the internal model. -/
example : ¬ MathlibNt.ChensTheorem.Semiprime 0 := by
  simp [MathlibNt.ChensTheorem.Semiprime]

example : ¬ MathlibNt.ChensTheorem.Semiprime 1 := by
  simp [MathlibNt.ChensTheorem.Semiprime]
