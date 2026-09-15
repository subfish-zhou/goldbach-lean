import MathlibNt.AnalyticNumberTheory.Vaughan.ProductionVaughanTypeIIRectangularSharpBridge
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanRectangularPrefixMaximalAmbient

/-!
# Honest rectangular maximal estimate for one actual Vaughan Type-II shell

This leaf identifies the actual collected-shell maximum with the exact sharp
rectangular maximum before applying the ambient prefix-maximal theorem.  Its
conclusion deliberately retains the rank-one right hand side and the literal
coefficient `L¹` mass.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The actual canonical collected-shell amplitude, with the maximum still over
all genuine hyperbolic endpoints `Y ≤ N`. -/
def vaughanActualCanonicalCollectedShellAmplitude
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare N u v k l q χ)

/-- The honest `q / φ(q)` weighted primitive mean of one actual canonical
collected shell over an arbitrary finite conductor family. -/
def vaughanActualCanonicalCollectedShellWeightedMean
    (N u v k l : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      vaughanActualCanonicalCollectedShellAmplitude N u v k l q χ

/-- On an active shell, the actual collected maximum is exactly the sharp
rectangular hyperbolic maximum, endpoint by endpoint. -/
theorem vaughanActualCanonicalCollectedShellAmplitude_eq_rectangularSharp
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanActualCanonicalCollectedShellAmplitude N u v k l q χ =
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) N
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) q χ := by
  unfold vaughanActualCanonicalCollectedShellAmplitude
  unfold rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
  congr 1
  unfold vaughanCanonicalCollectedPrefixMaxSquare
  unfold rectangularSharpHyperbolicPrefixMaxSquareUpTo
  congr 1
  apply Finset.image_congr
  intro Y hY
  dsimp only
  rw [vaughanTypeIICanonicalBilinearBlock_eq_rectangularSharp
    Y N u v k l q χ (Nat.le_of_lt_succ (Finset.mem_range.mp hY)) hactive]

/-- The actual weighted mean is literally the ambient sharp rectangular mean. -/
theorem vaughanActualCanonicalCollectedShellWeightedMean_eq_rectangularSharp
    (N u v k l : ℕ) (S : Finset ℕ)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanActualCanonicalCollectedShellWeightedMean N u v k l S =
      rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
        (vaughanTypeIIRectLeftCoeff N u k)
        (vaughanTypeIIRectRightCoeff N v l) N
        ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
        (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) S := by
  unfold vaughanActualCanonicalCollectedShellWeightedMean
  unfold rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro χ hχ
  exact vaughanActualCanonicalCollectedShellAmplitude_eq_rectangularSharp
    N u v k l q χ hactive

/-- Honest per-shell rectangular prefix-maximal bound.  No attempt is made to
scalarize either the rank-one energy term or the coefficient-family `L¹` term. -/
theorem vaughanActualCanonicalCollectedShellWeightedMean_le
    (N Q u v k l : ℕ) (hN : 3 ≤ N) (hQ : 0 < Q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hactive : (k, l) ∈ vaughanTypeIIActiveCanonicalRectangles N u v) :
    vaughanActualCanonicalCollectedShellWeightedMean N u v k l S ≤
      (1 / 2 + (14 * Real.log ((2 * N : ℕ) : ℝ) + 4) / Real.pi) *
        rankOneRectangularLSRHS
          (vaughanTypeIIRectLeftCoeff N u k)
          (vaughanTypeIIRectRightCoeff N v l)
          ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
          (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q +
      (8 / (Real.pi * ((2 * N : ℕ) : ℝ))) *
        rectangularCoefficientL1
          (vaughanTypeIIRectLeftCoeff N u k)
          (vaughanTypeIIRectRightCoeff N v l)
          ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
          (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) *
        weightedPrimitiveFamilyMass S := by
  rw [vaughanActualCanonicalCollectedShellWeightedMean_eq_rectangularSharp
    N u v k l S hactive]
  have hcorner : 2 ^ k * 2 ^ l ≤ N :=
    (mem_vaughanTypeIIActiveCanonicalRectangles.mp hactive).2
  have hkpos : 0 < 2 ^ k := by positivity
  have hlpos : 0 < 2 ^ l := by positivity
  have hkN : 2 ^ k ≤ N := by
    exact (le_mul_of_one_le_right (Nat.zero_le _) (Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ (by norm_num)))).trans hcorner
  have hlDiv : 2 ^ l ≤ N / 2 ^ k :=
    (Nat.le_div_iff_mul_le hkpos).2 (by simpa [mul_comm] using hcorner)
  have hkone : (1 : ℤ) ≤ (2 ^ k : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hlone : (1 : ℤ) ≤ (2 ^ l : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)))
  have hmEnd : (2 ^ k : ℤ) - 1 + (2 ^ k : ℕ) =
      (2 : ℤ) * (2 ^ k : ℕ) - 1 := by
    push_cast
    ring
  have hnEnd : (2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ) =
      (N / 2 ^ k : ℕ) := by
    rw [Nat.cast_add, Nat.cast_sub hlDiv]
    push_cast
    ring
  -- Normalize each rectangular interval once, then reuse its bounds below.
  have hmBounds : ∀ m ∈ Finset.Icc ((2 ^ k : ℤ) - 1 + 1)
      ((2 ^ k : ℤ) - 1 + (2 ^ k : ℕ)),
      1 ≤ m ∧ m ≤ (2 : ℤ) * (2 ^ k : ℕ) - 1 := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    rw [hmEnd] at hm'
    omega
  have hnBounds : ∀ n ∈ Finset.Icc ((2 ^ l : ℤ) - 1 + 1)
      ((2 ^ l : ℤ) - 1 + (N / 2 ^ k - 2 ^ l + 1 : ℕ)),
      1 ≤ n ∧ n ≤ (N / 2 ^ k : ℕ) := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    rw [hnEnd] at hn'
    omega
  apply rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo_le
    (vaughanTypeIIRectLeftCoeff N u k)
    (vaughanTypeIIRectRightCoeff N v l)
    ((2 ^ k : ℤ) - 1) ((2 ^ l : ℤ) - 1)
    (2 ^ k) (N / 2 ^ k - 2 ^ l + 1) Q N (2 * N)
    hQ S hS (by omega) (by omega)
  · intro m hm
    exact (hmBounds m hm).1
  · intro m hm
    have hmUpper := (hmBounds m hm).2
    have hkcast : ((2 ^ k : ℕ) : ℤ) ≤ N := by exact_mod_cast hkN
    omega
  · intro n hn
    exact (hnBounds n hn).1
  · intro n hn
    have hnUpper := (hnBounds n hn).2
    have hdivN : N / 2 ^ k ≤ N := Nat.div_le_self _ _
    have hdivN' : ((N / 2 ^ k : ℕ) : ℤ) ≤ N := by exact_mod_cast hdivN
    omega
  · intro m hm n hn
    nlinarith only [(hmBounds m hm).1, (hnBounds n hn).1]
  · intro m hm n hn
    have hm' := hmBounds m hm
    have hn' := hnBounds n hn
    have hmUpper : m ≤ (2 : ℤ) * (2 ^ k : ℕ) := by omega
    have hnUpper : n ≤ (N / 2 ^ k : ℕ) := hn'.2
    have hmulDiv : 2 ^ k * (N / 2 ^ k) ≤ N := Nat.mul_div_le N (2 ^ k)
    have hnnonneg : 0 ≤ n := by omega
    calc
      m * n ≤ ((2 : ℤ) * (2 ^ k : ℕ)) * n :=
        mul_le_mul_of_nonneg_right hmUpper hnnonneg
      _ ≤ ((2 : ℤ) * (2 ^ k : ℕ)) * (N / 2 ^ k : ℕ) :=
        mul_le_mul_of_nonneg_left hnUpper (by positivity)
      _ = (2 : ℤ) * ((2 ^ k : ℕ) * (N / 2 ^ k : ℕ)) := by ring
      _ ≤ (2 : ℤ) * N := by
        gcongr
        exact_mod_cast hmulDiv

end
end AnalyticNumberTheory.LargeSieve
