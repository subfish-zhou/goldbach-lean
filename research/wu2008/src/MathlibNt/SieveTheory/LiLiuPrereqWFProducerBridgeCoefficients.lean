import MathlibNt.SieveTheory.LiLiuPrereqWFRounding

/-!
# Natural producer formulas for the actual real-level coefficients

These equalities expose exactly the natural-number prefix tests and the
parity sign used by `LinearSieve.lean` in the frozen source. They prove
the formulas for the existing local functions; they do not introduce a
second weight or assume equality to it.

This module itself needs no producer import. The checked named-producer
identification is in `LiLiuPrereqWFProducerBridge`.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

theorem lowerAdmissibleSet_iff_natCeil (L : ℝ) (s : Finset ℕ) :
    LowerAdmissibleSet L s ↔
      ∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
        (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊ := by
  simp only [LowerAdmissibleSet, Nat.lt_ceil, Nat.cast_mul, Nat.cast_pow]

theorem upperAdmissibleSet_iff_natCeil (L : ℝ) (s : Finset ℕ) :
    UpperAdmissibleSet L s ↔
      ∀ p ∈ s, ¬Even ((s.filter (fun q => p ≤ q)).card) →
        (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊ := by
  simp only [UpperAdmissibleSet, Nat.lt_ceil, Nat.cast_mul, Nat.cast_pow]

/-- The entire lower coefficient, including its support and parity sign. -/
theorem lowerWeight_eq_natCeil_tests (M n : ℕ) (L : ℝ) :
    lowerWeight M L n =
      if n ∈ M.divisors ∧ n < ⌈L⌉₊ ∧
          (∀ p ∈ n.primeFactors,
            Even ((n.primeFactors.filter (fun q => p ≤ q)).card) →
              (n.primeFactors.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
      then if Even n.primeFactors.card then 1 else -1
      else 0 := by
  simp only [lowerWeight_apply, lowerAdmissibleSet_iff_natCeil,
    neg_one_pow_eq_ite, Nat.lt_ceil]

/-- The upper condition is the odd-position test, not the lower even test. -/
theorem upperWeight_eq_natCeil_tests (M n : ℕ) (L : ℝ) :
    upperWeight M L n =
      if n ∈ M.divisors ∧ n < ⌈L⌉₊ ∧
          (∀ p ∈ n.primeFactors,
            ¬Even ((n.primeFactors.filter (fun q => p ≤ q)).card) →
              (n.primeFactors.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
      then if Even n.primeFactors.card then 1 else -1
      else 0 := by
  simp only [upperWeight_apply, upperAdmissibleSet_iff_natCeil,
    neg_one_pow_eq_ite, Nat.lt_ceil]

theorem setWeight_eq_natCeil_tests (L : ℝ) (s : Finset ℕ) :
    setWeight L s =
      if s.prod id < ⌈L⌉₊ ∧
          (∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
            (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
      then if Even s.card then 1 else -1
      else 0 := by
  simp only [setWeight, lowerAdmissibleSet_iff_natCeil, Nat.lt_ceil]

theorem upperSetWeight_eq_natCeil_tests (L : ℝ) (s : Finset ℕ) :
    upperSetWeight L s =
      if s.prod id < ⌈L⌉₊ ∧
          (∀ p ∈ s, ¬Even ((s.filter (fun q => p ≤ q)).card) →
            (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
      then if Even s.card then 1 else -1
      else 0 := by
  simp only [upperSetWeight, upperAdmissibleSet_iff_natCeil, Nat.lt_ceil]

theorem lowerSetDensity_eq_natCeil_tests (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) :
    lowerSetDensity L g B =
      ∑ s ∈ B.powerset,
        (if s.prod id < ⌈L⌉₊ ∧
            (∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
              (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
          then if Even s.card then 1 else -1
          else 0) * ∏ p ∈ s, g p := by
  simp only [lowerSetDensity, setWeight_eq_natCeil_tests]

theorem upperSetDensity_eq_natCeil_tests (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) :
    upperSetDensity L g B =
      ∑ s ∈ B.powerset,
        (if s.prod id < ⌈L⌉₊ ∧
            (∀ p ∈ s, ¬Even ((s.filter (fun q => p ≤ q)).card) →
              (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
          then if Even s.card then 1 else -1
          else 0) * ∏ p ∈ s, g p := by
  simp only [upperSetDensity, upperSetWeight_eq_natCeil_tests]

#check lowerWeight_eq_natCeil_tests
#check upperWeight_eq_natCeil_tests
#print axioms lowerWeight_eq_natCeil_tests
#print axioms upperWeight_eq_natCeil_tests
#print axioms lowerSetDensity_eq_natCeil_tests
#print axioms upperSetDensity_eq_natCeil_tests

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
