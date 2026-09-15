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

@[simp]
theorem smallDensityBoundingSieve_nu :
    (smallDensityBoundingSieve P D ε g hgm hg).nu = g := rfl

@[simp]
theorem smallDensityBoundingSieve_primeFactors :
    (smallDensityBoundingSieve P D ε g hgm hg).prodPrimes.primeFactors =
      nonzeroDensityPrimes (geometricSmallPrimes P D ε) g :=
  densityBoundingSieve_primeFactors _ _ _ _ _

/-- These are the exact cutoff and level hypotheses of the finite producers. -/
theorem smallDensityBoundingSieve_cutoffs
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ ⌈D ^ (ε ^ 2)⌉₊ ∧ ⌈D ^ (ε ^ 2)⌉₊ ≤ ⌈D ^ ε⌉₊ ∧
      ∀ p ∈ (smallDensityBoundingSieve P D ε g hgm hg).prodPrimes.primeFactors,
        p < ⌈D ^ ε⌉₊ ∧ p < ⌈D ^ (ε ^ 2)⌉₊ := by
  obtain ⟨hz2, hzR⟩ := small_rounded_cutoff_bounds hD hε hε1
  refine ⟨hz2, hzR, ?_⟩
  intro p hp
  have hpu : p < ⌈D ^ (ε ^ 2)⌉₊ :=
    densityBoundingSieve_prime_lt_ceil (geometricSmallPrimes P D ε)
      (smallPrimes_prime P D ε) g hgm hg
      (fun q hq => (Finset.mem_filter.mp hq).2.2) p hp
  exact ⟨hpu.trans_le hzR, hpu⟩

theorem smallDensityBoundingSieve_rounded_carrier
    (hD : 2 ≤ D) (hε : 0 < ε) :
    (smallDensityBoundingSieve P D ε g hgm hg).prodPrimes.primeFactors.filter
      (fun p => p <
        ⌈(⌈D ^ ε⌉₊ : ℝ) ^
          (1 / roundedSieveCoordinate (D ^ ε) (D ^ (ε ^ 2)))⌉₊) =
      nonzeroDensityPrimes (geometricSmallPrimes P D ε) g := by
  exact densityBoundingSieve_rounded_carrier (geometricSmallPrimes P D ε)
    (smallPrimes_prime P D ε) g hgm hg
    (Real.one_lt_rpow (by linarith) hε)
    (Real.one_lt_rpow (by linarith) (sq_pos_of_pos hε))
    (fun p hp => (Finset.mem_filter.mp hp).2.2)

/-- Both main sums are the densities of the original named small weights,
not of a substituted family. This identity imposes no sign restriction on
`D` or `ε`; the support is the actual finite set in their definitions. -/
theorem smallDensityBoundingSieve_mainSums :
    let B := geometricSmallPrimes P D ε
    let S := smallDensityBoundingSieve P D ε g hgm hg
    S.mainSum (lowerWeight S.prodPrimes (⌈D ^ ε⌉₊ : ℝ)) =
        ∑ d ∈ (B.prod id).divisors, lowerSmallWeight P D ε d * g d ∧
    S.mainSum (upperWeight S.prodPrimes (⌈D ^ ε⌉₊ : ℝ)) =
        ∑ d ∈ (B.prod id).divisors, upperSmallWeight P D ε d * g d :=
  densityBoundingSieve_mainSums (geometricSmallPrimes P D ε)
    (smallPrimes_prime P D ε) g hgm hg (D ^ ε)

theorem smallDensityBoundingSieve_mainSums_eq_fullDefects
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let B := geometricSmallPrimes P D ε
    let S := smallDensityBoundingSieve P D ε g hgm hg
    S.mainSum (lowerWeight S.prodPrimes (⌈D ^ ε⌉₊ : ℝ)) =
        (∏ p ∈ B, (1 - g p)) -
          lowerDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) ∧
    S.mainSum (upperWeight S.prodPrimes (⌈D ^ ε⌉₊ : ℝ)) =
        (∏ p ∈ B, (1 - g p)) +
          upperDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) := by
  exact densityBoundingSieve_mainSums_eq_fullDefects (geometricSmallPrimes P D ε)
    (smallPrimes_prime P D ε) g hgm hg (Real.one_lt_rpow (by linarith) hε)
    (fun _ hp => smallPrime_lt_level P (by linarith) hε.le hε1 hp)

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

#check smallDensityBoundingSieve
#print axioms smallDensityBoundingSieve_cutoffs
#print axioms smallDensityBoundingSieve_rounded_carrier
#print axioms smallDensityBoundingSieve_mainSums
#print axioms smallDensityBoundingSieve_mainSums_eq_fullDefects
#print axioms smallDensityBoundingSieve_localProduct

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
