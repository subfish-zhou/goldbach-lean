

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowHighConductor

/-!
 # Exact lambda-prefix to low/high conductor connector

This module closes the finite normalization gap between the natural-number
prefix used by Standard-BV character orthogonality and the integer interval
prefix used by conductor regrouping.  It then applies the exact low/high
Finset partition, with no analytic hypothesis.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The natural Chebyshev character prefix is exactly the integer interval
prefix used by the conductor machinery.  The only extra natural term is zero,
and `Λ(0)=0`. -/
theorem lambdaCharacterPrefix_eq_integerInterval
    (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    lambdaCharacterPrefix y q χ =
      ∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
        vonMangoldtIntegerCoeff n * χ (n : ZMod q) := by
  have hrange : Finset.range (y + 1) = insert 0 (Finset.Icc 1 y) := by
    ext n
    simp
    omega
  have hnatInt :
      (∑ n ∈ Finset.Icc 1 y, lambdaNatCoeff n * χ (n : ZMod q)) =
        ∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
          vonMangoldtIntegerCoeff n * χ (n : ZMod q) := by
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      have h := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · intro a₁ ha₁ a₂ ha₂ h
      exact_mod_cast h
    · intro z hz
      have hz' := Finset.mem_Icc.mp hz
      have hz0 : 0 ≤ z := by omega
      refine ⟨z.toNat, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · simpa using Int.toNat_le_toNat hz'.1
      · rw [← Int.ofNat_le]
        simpa [Int.toNat_of_nonneg hz0] using hz'.2
      · exact Int.toNat_of_nonneg hz0
    · intro n hn
      simp [lambdaNatCoeff, vonMangoldtIntegerCoeff]
  unfold lambdaCharacterPrefix
  rw [hrange, Finset.sum_insert]
  · simpa [lambdaNatCoeff] using hnatInt
  · simp

/-- The squared norm of every natural lambda prefix is one of the values in the
integer-prefix maximum. -/
theorem norm_lambdaCharacterPrefix_sq_le_characterPrefixMaxSquare
    (N y q : ℕ) (hy : y ≤ N) (χ : DirichletCharacter ℂ q) :
    ‖lambdaCharacterPrefix y q χ‖ ^ 2 ≤
      characterPrefixMaxSquare χ vonMangoldtIntegerCoeff 0 N := by
  rw [lambdaCharacterPrefix_eq_integerInterval]
  unfold characterPrefixMaxSquare
  apply Finset.le_max'
  refine Finset.mem_image.mpr ⟨y, ?_, ?_⟩
  · simpa [Finset.mem_range] using hy
  · unfold characterPrefixSquare
    norm_num

/-- The natural prefix maximum from character orthogonality is bounded by the
square-root integer prefix maximum used by conductor regrouping. -/
theorem lambdaCharacterPrefixMaxAmplitude_le_nonprincipalPrefixAmplitude
    (N q : ℕ) (χ : DirichletCharacter ℂ q) :
    lambdaCharacterPrefixMaxAmplitude N q χ ≤
      nonprincipalPrefixAmplitude vonMangoldtIntegerCoeff N q χ := by
  unfold lambdaCharacterPrefixMaxAmplitude
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  -- Pass from the squared-prefix bound to the square-root amplitude directly.
  exact Real.le_sqrt_of_sq_le
    (norm_lambdaCharacterPrefix_sq_le_characterPrefixMaxSquare N y q hyN χ)

/-- The literal lambda nonprincipal mean is bounded by the all-character mean
already consumed by the conductor theorem. -/
theorem nonprincipalLambdaPhysical_le_directAllCharacterMean (N Q : ℕ) :
    nonprincipalLambdaPhysical N Q ≤
      directAllCharacterMean vonMangoldtIntegerCoeff N Q := by
  unfold nonprincipalLambdaPhysical directAllCharacterMean
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun χ hχ =>
      lambdaCharacterPrefixMaxAmplitude_le_nonprincipalPrefixAmplitude N q χ
  · positivity

/-- Exact, premise-free lambda-to-low/high conductor connector. -/
theorem lambdaToLowHighConductorConnector
    (N Q C : ℕ) :
    nonprincipalLambdaPhysical N Q ≤
      2 * (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
  calc
    nonprincipalLambdaPhysical N Q ≤
        directAllCharacterMean vonMangoldtIntegerCoeff N Q :=
      nonprincipalLambdaPhysical_le_directAllCharacterMean N Q
    _ ≤ 2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q :=
      directAllCharacterMean_le_conductor vonMangoldtIntegerCoeff N Q
    _ = 2 * (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
      rw [directConductorMean_low_high vonMangoldtIntegerCoeff N Q C]
      rfl

end

end AnalyticNumberTheory.LargeSieve
