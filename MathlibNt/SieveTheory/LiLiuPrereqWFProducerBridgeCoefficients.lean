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


theorem setWeight_eq_natCeil_tests (L : ℝ) (s : Finset ℕ) :
    setWeight L s =
      if s.prod id < ⌈L⌉₊ ∧
          (∀ p ∈ s, Even ((s.filter (fun q => p ≤ q)).card) →
            (s.filter (fun q => p ≤ q)).prod id * p ^ 2 < ⌈L⌉₊)
      then if Even s.card then 1 else -1
      else 0 := by
  simp only [setWeight, lowerAdmissibleSet_iff_natCeil, Nat.lt_ceil]


end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
