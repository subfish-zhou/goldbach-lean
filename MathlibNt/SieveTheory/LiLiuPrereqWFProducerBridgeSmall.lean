import MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeSieve

/-!
# The genuine density sieve for the actual small-prime family

This specializes the checked finite construction to `geometricSmallPrimes`.
Only densities below the actual cutoff are constrained. The product bound is
first truncated at that cutoff and then transported through zero deletion.
No moving-range or analytic estimate is used here.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset
open scoped Classical

noncomputable def smallDensityBoundingSieve (P : Finset ℕ) (D ε : ℝ)
    (g : ArithmeticFunction ℝ) (hgm : g.IsMultiplicative)
    (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1) : BoundingSieve :=
  densityBoundingSieve (geometricSmallPrimes P D ε) (smallPrimes_prime P D ε) g hgm hg

variable (P : Finset ℕ) (D ε : ℝ) (g : ArithmeticFunction ℝ)
  (hgm : g.IsMultiplicative)
  (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1)


/-- The exact expanded producer product hypothesis, with the same `K` and
the non-strict diagonal case included. No conditions on `g` above `D^(ε²)`
are added by restricting the carrier. -/
theorem smallDensityBoundingSieve_localProduct {K : ℝ} (hK : 0 ≤ K)
    (hdim : DimensionOneProductBound P g K) :
    let S := smallDensityBoundingSieve P D ε g hgm hg
    ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∏ p ∈ S.prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z), (1 - S.nu p)⁻¹) ≤
          Real.log z / Real.log w * (1 + K / Real.log w) := by
  exact densityBoundingSieve_localProduct (geometricSmallPrimes P D ε)
    (smallPrimes_prime P D ε) g hgm hg hK
    (dimensionOneProductBound_truncate hdim hK (D ^ (ε ^ 2)))

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
