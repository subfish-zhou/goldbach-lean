import MathlibNt.AnalyticNumberTheory.LargeSieve.HighConductorDyadicPrimitive
import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

def vaughanTypeIRowCoefficient (a : ℂ) (b : ℤ → ℂ) (n : ℤ) : ℂ := a * b n

def highConductorVaughanTypeIRowAmplitude
    (a : ℂ) (b : ℤ → ℂ) (M : ℤ) (L d : ℕ)
    (χ : PrimitiveCharacter d) : ℝ :=
  Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeIRowCoefficient a b) M L d χ)

private theorem highConductor_subset_full {R Q : ℕ} :
    Finset.Ioc R Q ⊆ Finset.Icc 1 Q := by
  intro d hd
  rw [Finset.mem_Ioc] at hd
  rw [Finset.mem_Icc]
  omega

theorem highConductorVaughanTypeIRow_squareLedger_le
    (R Q L : ℕ) (hQ : 0 < Q) (a : ℂ) (b : ℤ → ℂ) (M : ℤ) :
    highConductorPrimitiveSquareLedger R Q
        (highConductorVaughanTypeIRowAmplitude a b M L) ≤
      (((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant L Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + L),
            ‖vaughanTypeIRowCoefficient a b n‖ ^ 2 := by
  unfold highConductorPrimitiveSquareLedger
  calc
    (∑ d ∈ Finset.Ioc R Q,
        ((d : ℝ) / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            (highConductorVaughanTypeIRowAmplitude a b M L d χ) ^ 2) =
      ∑ d ∈ Finset.Ioc R Q,
        ((d : ℝ) / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            primitiveCharacterPrefixMaxSquare
              (vaughanTypeIRowCoefficient a b) M L d χ := by
        simp only [highConductorVaughanTypeIRowAmplitude,
          Real.sq_sqrt (primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ _)]
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
        ((d : ℝ) / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            primitiveCharacterPrefixMaxSquare
              (vaughanTypeIRowCoefficient a b) M L d χ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg highConductor_subset_full
        intro d hd hnot
        exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun χ hχ =>
            primitiveCharacterPrefixMaxSquare_nonneg
              (vaughanTypeIRowCoefficient a b) M L d χ)
    _ ≤ _ := weighted_primitive_prefix_maximal
      (vaughanTypeIRowCoefficient a b) M L Q hQ

/-- Expanding the fixed Vaughan Type-I row coefficient inserts its outer
coefficient energy exactly once. -/
theorem vaughanTypeIRowCoefficient_energy_eq
    (a : ℂ) (b : ℤ → ℂ) (M : ℤ) (L : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + L),
        ‖vaughanTypeIRowCoefficient a b n‖ ^ 2) =
      ‖a‖ ^ 2 * ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2 := by
  simp_rw [vaughanTypeIRowCoefficient, norm_mul, mul_pow]
  rw [Finset.mul_sum]

/-- Actual fixed-row high-conductor Type-I square ledger after row-coefficient
expansion.  This is a direct consequence of character orthogonality/large sieve;
there is no conclusion-shaped square-saving premise. -/
theorem highConductorVaughanTypeIRow_squareLedger_le_expanded
    (R Q L : ℕ) (hQ : 0 < Q) (a : ℂ) (b : ℤ → ℂ) (M : ℤ) :
    highConductorPrimitiveSquareLedger R Q
        (highConductorVaughanTypeIRowAmplitude a b M L) ≤
      (((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant L Q *
          (‖a‖ ^ 2 * ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2) := by
  rw [← vaughanTypeIRowCoefficient_energy_eq]
  exact highConductorVaughanTypeIRow_squareLedger_le R Q L hQ a b M

/-- The AP-normalized `1/φ(d)` mean for one actual Type-I row.  The exact
high-conductor restriction survives both Cauchy steps.  Its square is controlled
by the harmonic tail times the proved, expanded physical row ledger. -/
theorem highConductorVaughanTypeIRow_mean_sq_le
    (R Q L : ℕ) (hQ : 0 < Q) (a : ℂ) (b : ℤ → ℂ) (M : ℤ) :
    (highConductorPrimitiveMean R Q
        (highConductorVaughanTypeIRowAmplitude a b M L)) ^ 2 ≤
      highConductorHarmonicTail R Q *
        ((((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant L Q *
            (‖a‖ ^ 2 *
              ∑ n ∈ Finset.Icc (M + 1) (M + L), ‖b n‖ ^ 2)) := by
  calc
    _ ≤ highConductorHarmonicTail R Q *
          highConductorPrimitiveSquareLedger R Q
            (highConductorVaughanTypeIRowAmplitude a b M L) :=
      highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger R Q _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (highConductorVaughanTypeIRow_squareLedger_le_expanded
        R Q L hQ a b M)
      (Finset.sum_nonneg fun d hd => by positivity)

end
end AnalyticNumberTheory.LargeSieve
