

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVExactLowHighConnector
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVLowSiegelWalfiszProducer

/-!
 # Pointwise prefix bounds imply primitive prefix-amplitude bounds

This file is the finite, honest bridge needed by a pointwise
Siegel--Walfisz theorem.  Its premise bounds every actual twisted prefix
through `N`; it does not assume the maximum that occurs in the conclusion.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- A bound for every integer prefix, including the empty prefix at `y = 0`,
bounds the square root of the primitive-character prefix-square maximum. -/
theorem primitivePrefixAmplitude_le_of_pointwise_integerPrefix
    (a : ℤ → ℂ) (N q : ℕ) (ψ : PrimitiveCharacter q) (B : ℝ)
    (hpointwise : ∀ y : ℕ, y ≤ N →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
        a n * ψ.1 (n : ZMod q)‖ ≤ B) :
    primitivePrefixAmplitude a N q ψ ≤ B := by
  have hB : 0 ≤ B := by
    have h0 := hpointwise 0 (Nat.zero_le N)
    simpa using h0
  have hmax : primitiveCharacterPrefixMaxSquare a 0 N q ψ ≤ B ^ 2 := by
    unfold primitiveCharacterPrefixMaxSquare
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    have hyN : y ≤ N := by
      simpa [Finset.mem_range] using hy
    unfold primitiveCharacterPrefixSquare
    simp only [zero_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpointwise y hyN) 2
  exact (sq_le_sq₀ (primitivePrefixAmplitude_nonneg a N q ψ) hB).mp
    ((primitivePrefixAmplitude_sq a N q ψ).trans_le hmax)

/-- A uniform pointwise bound for the natural-number Chebyshev twists bounds
the primitive prefix amplitude.  The conversion uses `Λ(0) = 0`, the exact
cast from `[1,y] ⊆ ℕ` to `[1,(y : ℤ)]`, and the underlying character `ψ.1`. -/
theorem primitivePrefixAmplitude_vonMangoldt_le_of_pointwise_lambdaCharacterPrefix
    (N q : ℕ) (ψ : PrimitiveCharacter q) (B : ℝ)
    (hpointwise : ∀ y : ℕ, y ≤ N →
      ‖lambdaCharacterPrefix y q ψ.1‖ ≤ B) :
    primitivePrefixAmplitude vonMangoldtIntegerCoeff N q ψ ≤ B := by
  apply primitivePrefixAmplitude_le_of_pointwise_integerPrefix
  intro y hy
  rw [← lambdaCharacterPrefix_eq_integerInterval]
  exact hpointwise y hy

/-- A future Siegel--Walfisz theorem uniform in every endpoint `y ≤ N` feeds
directly into the exact nonprincipal primitive source used by Standard BV.
The hypothesis is pointwise in `y`, rather than a renamed amplitude bound. -/
theorem nonprincipalPrimitivePsiSiegelWalfiszSource_of_pointwise_lambdaCharacterPrefix
    (hpointwise :
      ∀ C D : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
          ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
            ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
              ∀ y : ℕ, y ≤ N →
                ‖lambdaCharacterPrefix y d ψ.1‖ ≤
                  K * (N : ℝ) / Real.log (N : ℝ) ^ D) :
    NonprincipalPrimitivePsiSiegelWalfiszSource := by
  intro C D
  obtain ⟨K, hK, hN⟩ := hpointwise C D
  refine ⟨K, hK, ?_⟩
  filter_upwards [hN] with N hN
  intro hN2 d hd ψ hψ
  exact primitivePrefixAmplitude_vonMangoldt_le_of_pointwise_lambdaCharacterPrefix
    N d ψ (K * (N : ℝ) / Real.log (N : ℝ) ^ D)
    (hN hN2 d hd ψ hψ)

end

end AnalyticNumberTheory.LargeSieve