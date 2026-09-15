import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserFiniteToContinuousFinalProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserWeightedAggregateTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAdaptiveDiscreteTail

/-!
# Exact final bridge for the upper Rosser density

This module isolates the exact finite bookkeeping between the explicit upper
Rosser weight and a fixed prefix plus one uniformly indexed boundary block.
The block has common length `P.card + 1 - T`, so it matches the weighted
aggregate-tail producer literally.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

private theorem sum_range_eq_prefix_add_padded_tail
    (f : ℕ → ℝ) {M C T : ℕ} (hMC : M ≤ C) (hTC : T ≤ C)
    (hzero : ∀ k, M ≤ k → f k = 0) :
    (∑ k ∈ Finset.range M, f k) =
      (∑ k ∈ Finset.range T, f k) +
        ∑ j ∈ Finset.range (C - T), f (T + j) := by
  have hMCsum : (∑ k ∈ Finset.range M, f k) = ∑ k ∈ Finset.range C, f k := by
    apply Finset.sum_subset (Finset.range_mono hMC)
    intro k hkC hkM
    exact hzero k (Nat.le_of_not_gt (by simpa using hkM))
  have hsplit := Finset.sum_range_add f T (C - T)
  have hadd : T + (C - T) = C := Nat.add_sub_of_le hTC
  rw [hadd] at hsplit
  rw [hMCsum, hsplit]

/-- Exact decomposition of the explicit upper Rosser main sum at an arbitrary
prefix threshold `T ≤ P.card+1`.  Every terminal uses the same remainder range
`P.card+1-T`; shorter terminal carriers are padded by identically zero relative
boundary layers.  Thus there is no off-by-one or terminal-dependent block
length left when invoking the weighted aggregate-tail theorem. -/
theorem mainSum_upperRosserWeight_eq_relativeBoundaryPrefix_add_paddedTail
    {S : BoundingSieve} {z Δ s : ℝ} (T : ℕ)
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s)
    (hT : T ≤ S.prodPrimes.primeFactors.card + 1) :
    S.mainSum
        (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) =
      (1 +
          (∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ k ∈ Finset.range T,
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) +
          ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range
                  (S.prodPrimes.primeFactors.card + 1 - T),
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) (T + j)) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  classical
  let P := S.prodPrimes.primeFactors
  let D := Nat.floor Δ + 1
  let V := ∏ p ∈ P, (1 - S.nu p)
  have hlevel : ∀ p ∈ P, p < D := by
    intro p hp
    exact lt_floor_add_one_of_le_of_log_ratio hz hΔ (hcut p hp) hs hslo
  have hD : 1 < D :=
    lt_floor_add_one_of_le_of_log_ratio hz hΔ (by norm_num; linarith) hs hslo
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p (hprime p hp) hpDvd))
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hdepth (q : ℕ) (hq : q ∈ P) :
      (∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu D q (P.filter (fun p => q < p)) k) =
        (∑ k ∈ Finset.range T,
          LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu D q (P.filter (fun p => q < p)) k) +
          ∑ j ∈ Finset.range (P.card + 1 - T),
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              S.nu D q (P.filter (fun p => q < p)) (T + j) := by
    apply sum_range_eq_prefix_add_padded_tail
    · exact Nat.add_le_add_right
        (Finset.card_le_card (Finset.filter_subset (fun p => q < p) P)) 1
    · simpa [P] using hT
    · intro k hk
      apply upperRosserBoundaryChainsFixedDepthRelativeDensity_eq_zero_of_carrierSupportDepth_le
      unfold upperRosserBoundaryCarrierSupportDepth
      omega
  have hratio :=
    LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
      S.nu P hD hprime hlevel hfactor
  have hsum :
      (∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
        ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
          LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu D q (P.filter (fun p => q < p)) k) =
        (∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
          ∑ k ∈ Finset.range T,
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              S.nu D q (P.filter (fun p => q < p)) k) +
        ∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
          ∑ j ∈ Finset.range (P.card + 1 - T),
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              S.nu D q (P.filter (fun p => q < p)) (T + j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hdepth q hq, mul_add]
  have hdecomp :
      LinearSieve.upperRosserSetDensitySum S.nu D P / V =
        1 +
          (∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
            ∑ k ∈ Finset.range T,
              LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                S.nu D q (P.filter (fun p => q < p)) k) +
          ∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
            ∑ j ∈ Finset.range (P.card + 1 - T),
              LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                S.nu D q (P.filter (fun p => q < p)) (T + j) := by
    simpa only [add_assoc] using
      hratio.trans (congrArg (fun x : ℝ => 1 + x) hsum)
  rw [LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  change LinearSieve.upperRosserSetDensitySum S.nu D P = _
  change _ = _ * V
  apply (div_eq_iff hV).mp
  simpa [P, D, V, AnalyticNumberTheory.Sieve.sieveProductPrimeFactors] using hdecomp

/-- The same exact bridge in the coordinates of the weighted aggregate-tail
producer.  The prefix threshold is literally `L+N`, while the remainder is
indexed literally by `L+j+N`; the common block length is
`P.card+1-(L+N)`. -/
theorem mainSum_upperRosserWeight_eq_relativeBoundaryPrefix_add_weightedTail
    {S : BoundingSieve} {z Δ s : ℝ} (L N : ℕ)
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s)
    (hLN : L + N ≤ S.prodPrimes.primeFactors.card + 1) :
    S.mainSum
        (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) =
      (1 +
          (∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ k ∈ Finset.range (L + N),
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) +
          ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range
                  (S.prodPrimes.primeFactors.card + 1 - (L + N)),
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p))
                  (L + j + N)) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    mainSum_upperRosserWeight_eq_relativeBoundaryPrefix_add_paddedTail
      (S := S) (z := z) (Δ := Δ) (s := s) (L + N)
      hz hΔ hcut hs hslo hLN

/-- The exact remaining analytic interface after the finite decomposition.
It deliberately keeps the Euler product on both sides.  An absolute estimate
`weightedTail * V ≤ τ L` with `τ L → 0` does not inhabit this interface: the
needed conclusion is at scale `ρ * V`, uniformly in the varying sieve. -/
def UpperRosserScaledPrefixTailComparison
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (_hH : SuzukiLemma144KappaOne.Section13HatSourceContract H) : Prop :=
  ∀ K ρ : ℝ, 1 < K → 0 < ρ →
    ∃ T : ℕ, ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
      let T' := min T (S.prodPrimes.primeFactors.card + 1)
      (1 +
          (∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ k ∈ Finset.range T',
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) +
          ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range
                  (S.prodPrimes.primeFactors.card + 1 - T'),
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) (T' + j)) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤
      (jurkatRichertUpperLinearSieveFactor s + ρ) *
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S

/-- Once the scale-faithful prefix-plus-tail comparison is supplied, the target
fundamental lemma follows with exactly the required `∃ z₀, ∀ S,z` order. -/
theorem dimensionOneUpperRosserDensityFundamentalLemma_of_scaledPrefixTail
    (H : SuzukiLemma144KappaOne.Section13HatLayers)
    (hH : SuzukiLemma144KappaOne.Section13HatSourceContract H)
    (hfinal : UpperRosserScaledPrefixTailComparison H hH) :
    DimensionOneUpperRosserDensityFundamentalLemma := by
  intro K ρ hK hρ
  obtain ⟨T, z₀, hbound⟩ := hfinal K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro S z Δ s hz₀ hz hΔ hlocal hcut hs hslo hshi
  let T' := min T (S.prodPrimes.primeFactors.card + 1)
  have hT' : T' ≤ S.prodPrimes.primeFactors.card + 1 := by
    exact min_le_right _ _
  rw [mainSum_upperRosserWeight_eq_relativeBoundaryPrefix_add_paddedTail
    T' hz hΔ hcut hs hslo hT']
  exact hbound S z Δ s hz₀ hz hΔ hlocal hcut hs hslo hshi


end

end MathlibNt.SieveTheory.SwitchingPrinciple
