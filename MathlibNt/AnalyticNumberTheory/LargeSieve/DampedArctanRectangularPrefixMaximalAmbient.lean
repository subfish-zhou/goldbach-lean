

import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanSelectorHyperbolicPrimitiveL1

/-!
 # Rectangular sharp hyperbolic prefix maxima with an ambient scale

This leaf separates the endpoint `H` over which the prefix maximum is taken
from the ambient support and damping scale `M` used by the selector estimate.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The largest squared sharp rectangular hyperbolic prefix norm for
`0 ≤ Y ≤ H`. -/
def rectangularSharpHyperbolicPrefixMaxSquareUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (H + 1)).image fun Y =>
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ^ 2).max'
    (by simp)

/-- Square-root amplitude of the maximal squared sharp rectangular prefix up
through endpoint `H`. -/
def rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (rectangularSharpHyperbolicPrefixMaxSquareUpTo a b H Ma Mb Na Nb q χ)

/-- Weighted primitive mean in which each character has its own maximizing
prefix endpoint bounded by `H`. -/
def rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo a b H Ma Mb Na Nb q χ

/-- Every maximal squared prefix up to `H` has an attaining endpoint `Y ≤ H`,
and its square-root amplitude is the norm at that endpoint. -/
theorem exists_rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo_eq
    (a b : ℤ → ℂ) (H : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) :
    ∃ Y ≤ H,
      rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo a b H Ma Mb Na Nb q χ =
        ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ := by
  let values : Finset ℝ :=
    (Finset.range (H + 1)).image fun Y =>
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ^ 2
  have hvalues : values.Nonempty := by
    dsimp [values]
    simp
  have hmax := Finset.max'_mem values hvalues
  rw [Finset.mem_image] at hmax
  obtain ⟨Y, hYrange, hYmax⟩ := hmax
  refine ⟨Y, ?_, ?_⟩
  · simpa [Finset.mem_range] using hYrange
  · unfold rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo
    unfold rectangularSharpHyperbolicPrefixMaxSquareUpTo
    change Real.sqrt (values.max' hvalues) = _
    rw [← hYmax]
    exact Real.sqrt_sq (norm_nonneg _)

/-- Character-wise maximal sharp hyperbolic rectangular primitive `L¹`
estimate with maximum endpoint `H` and independent ambient support/damping
scale `M`.  Once `H ≤ M`, the estimate is a direct application of the selector
bound, so all constants are measured at `M`. -/
theorem rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo_le
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q H M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M) (hHM : H ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ))
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
        a b H Ma Mb Na Nb S ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  choose Y hYH hYattain using fun q χ =>
    exists_rectangularSharpHyperbolicPrefixMaxAmplitudeUpTo_eq
      a b H Ma Mb Na Nb q χ
  have hYM : ∀ q χ, Y q χ ≤ M := fun q χ => (hYH q χ).trans hHM
  unfold rectangularSharpHyperbolicPrefixMaxWeightedPrimitiveMeanUpTo
  simp_rw [hYattain]
  exact selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le
    a b Y Ma Mb Na Nb Q M hQ S hS hM hYM hm1 hmM hn1 hnM hmnPos hmnM

end

end AnalyticNumberTheory.LargeSieve
