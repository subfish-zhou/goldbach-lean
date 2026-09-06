import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserTerminalSplitBridge

/-!
# Weighted aggregate tail for the upper Rosser boundary

The production prefix carries the normalized outer atom
`S.nu q / (1 - S.nu q)`.  Keeping this atom and restoring the complete Euler
product cancels the terminal-dependent suffix denominator.  The remaining
ordered terminal masses telescope to at most one, so no terminal cardinality
appears.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Filter Topology

noncomputable section

/-- Literal geometric form of the weighted aggregate tail.  The constants are
selected before every sieve and source parameter.  This is the form intended to
compose with a fixed-depth prefix producer. -/
theorem exists_upperRosserBoundaryChains_weightedAggregate_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BoundingSieve) (L n : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        ((∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range n,
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p))
                  (L + j + N)) *
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤
            90 * C * (9 / 10 : ℝ) ^ L) := by
  obtain ⟨N, C, hC, hdepth⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_eventually_geometric K hK
  refine ⟨N, C, hC, ?_⟩
  intro S L n z Δ s hz hΔ hs hlocal hcut
  let P := S.prodPrimes.primeFactors
  let B : ℕ → ℝ := fun q =>
    ∑ j ∈ Finset.range n,
      LinearSieve.upperRosserBoundaryChainsFixedDepthDensity S.nu
        (Nat.floor Δ + 1) q (P.filter (fun p => q < p)) (L + j + N)
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd))
  have hterminal : ∀ q ∈ P,
      0 ≤ S.nu q * ∏ p ∈ P.filter (fun p => p < q), (1 - S.nu p) := by
    intro q hq
    apply mul_nonneg
    · have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqDvd : q ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hq |>.2
      exact (S.nu_pos_of_prime q hqPrime hqDvd).le
    · apply Finset.prod_nonneg
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
      have hpDvd : p ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpP |>.2
      exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd).le
  have hraw : ∀ q ∈ P, B q ≤ 90 * C * (9 / 10 : ℝ) ^ L := by
    intro q hq
    have hmono : B q ≤
        ∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q (P.filter (fun p => q < p))
            (L + j + N) := by
      dsimp [B]
      apply Finset.sum_le_sum
      intro j hj
      apply LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_mono
      · intro p hp
        have hpP := (Finset.mem_filter.mp hp).1
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
        have hpDvd : p ∣ S.prodPrimes :=
          (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpP |>.2
        exact (S.nu_pos_of_prime p hpPrime hpDvd).le
      · intro p hp
        exact nu_le_nu_div_one_sub_of_mem (Finset.mem_filter.mp hp).1
    have hterms :
        (∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p))
            (Nat.floor Δ + 1) q (P.filter (fun p => q < p))
            (L + j + N)) ≤
          ∑ j ∈ Finset.range n, 9 * C * (9 / 10 : ℝ) ^ (L + j) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [P] using hdepth S (L + j) q z Δ s hz hΔ hs hlocal hcut hq
    have hgeom : (∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j) ≤ 10 := by
      calc
        (∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j) ≤
            ∑' j : ℕ, (9 / 10 : ℝ) ^ j :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum
            (Finset.range n) (by intro j hj; positivity)
        _ = (1 - (9 / 10 : ℝ))⁻¹ :=
          tsum_geometric_of_lt_one (by norm_num) (by norm_num)
        _ = 10 := by norm_num
    calc
      B q ≤ _ := hmono
      _ ≤ ∑ j ∈ Finset.range n, 9 * C * (9 / 10 : ℝ) ^ (L + j) := hterms
      _ = (9 * C * (9 / 10 : ℝ) ^ L) *
          ∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ ≤ (9 * C * (9 / 10 : ℝ) ^ L) * 10 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 90 * C * (9 / 10 : ℝ) ^ L := by ring
  have hterminalSum :
      (∑ q ∈ P, S.nu q *
        ∏ p ∈ P.filter (fun p => p < q), (1 - S.nu p)) ≤ 1 := by
    simpa [P] using sum_nu_mul_prod_one_sub_lt_le_one S
  have hrelative (q : ℕ) :
      (∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q (P.filter (fun p => q < p))
          (L + j + N)) =
        B q / ∏ p ∈ P.filter (fun p => q < p), (1 - S.nu p) := by
    unfold LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
    rw [← Finset.sum_div]
  change ((∑ q ∈ P, (S.nu q / (1 - S.nu q)) *
      ∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q (P.filter (fun p => q < p))
          (L + j + N)) *
        ∏ p ∈ P, (1 - S.nu p) ≤ 90 * C * (9 / 10 : ℝ) ^ L)
  rw [Finset.sum_mul]
  calc
    (∑ q ∈ P, ((S.nu q / (1 - S.nu q)) *
        ∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu (Nat.floor Δ + 1) q (P.filter (fun p => q < p))
            (L + j + N)) *
          ∏ p ∈ P, (1 - S.nu p)) =
      ∑ q ∈ P, (S.nu q *
        ∏ p ∈ P.filter (fun p => p < q), (1 - S.nu p)) * B q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hrelative q]
      exact normalizedBoundaryTail_mul_eulerProduct_eq_orderedMass
        hq hfactor (B q)
    _ ≤ ∑ q ∈ P, (S.nu q *
        ∏ p ∈ P.filter (fun p => p < q), (1 - S.nu p)) *
          (90 * C * (9 / 10 : ℝ) ^ L) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hraw q hq) (hterminal q hq)
    _ = (90 * C * (9 / 10 : ℝ) ^ L) *
        ∑ q ∈ P, S.nu q *
          ∏ p ∈ P.filter (fun p => p < q), (1 - S.nu p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (90 * C * (9 / 10 : ℝ) ^ L) * 1 :=
      mul_le_mul_of_nonneg_left hterminalSum (by positivity)
    _ = 90 * C * (9 / 10 : ℝ) ^ L := by ring

/-- Geometric weighted tail on any terminal subcarrier, with no cardinality
factor.  Taking `T` to be a filtered terminal lane gives the exact aggregate
replacement for the old pointwise-then-cardinality estimate. -/
theorem exists_upperRosserBoundaryChains_weightedSubaggregate_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BoundingSieve) (T : Finset ℕ) (L n : ℕ) (z Δ s : ℝ),
        T ⊆ S.prodPrimes.primeFactors →
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        ((∑ q ∈ T,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range n,
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p))
                  (L + j + N)) *
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤
            90 * C * (9 / 10 : ℝ) ^ L) := by
  obtain ⟨N, C, hC, hfull⟩ :=
    exists_upperRosserBoundaryChains_weightedAggregate_geometric K hK
  refine ⟨N, C, hC, ?_⟩
  intro S T L n z Δ s hT hz hΔ hs hlocal hcut
  let P := S.prodPrimes.primeFactors
  let F : ℕ → ℝ := fun q =>
    (S.nu q / (1 - S.nu q)) *
      ∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (P.filter (fun p => q < p)) (L + j + N)
  have hF : ∀ q ∈ P, 0 ≤ F q := by
    intro q hq
    apply mul_nonneg (nu_div_one_sub_nonneg_of_mem hq)
    apply Finset.sum_nonneg
    intro j hj
    apply LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity_nonneg
    · intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
      have hpDvd : p ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpP |>.2
      exact (S.nu_pos_of_prime p hpPrime hpDvd).le
    · intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpP
      have hpDvd : p ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpP |>.2
      exact (S.nu_lt_one_of_prime p hpPrime hpDvd).le
  have hprod : 0 ≤ ∏ p ∈ P, (1 - S.nu p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd).le
  have hsum : (∑ q ∈ T, F q) ≤ ∑ q ∈ P, F q :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun q hqP hqT => hF q hqP)
  calc
    (∑ q ∈ T, F q) * ∏ p ∈ P, (1 - S.nu p) ≤
        (∑ q ∈ P, F q) * ∏ p ∈ P, (1 - S.nu p) :=
      mul_le_mul_of_nonneg_right hsum hprod
    _ ≤ 90 * C * (9 / 10 : ℝ) ^ L := by
      simpa [P, F] using hfull S L n z Δ s hz hΔ hs hlocal hcut

/-- The existing ordered-mass telescoping estimate, rewritten in the literal
fixed-depth prefix coordinates: normalized outer atom times relative boundary
density.  The cutoff `N` and tail `τ` are selected before the sieve, depth block,
and source parameters. -/
theorem exists_upperRosserBoundaryChains_weightedAggregate_uniform_tail
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (nhds 0) ∧
      (∀ L, 0 ≤ τ L) ∧
      ∀ (S : BoundingSieve) (L n : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        ((∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range n,
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p))
                  (L + j + N)) *
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤ τ L) := by
  obtain ⟨N, τ, hτ, hτnonneg, htail⟩ :=
    exists_upperRosserBoundaryChains_global_uniform_absolute_tail K hK
  refine ⟨N, τ, hτ, hτnonneg, ?_⟩
  intro S L n z Δ s hz hΔ hs hlocal hcut
  simpa only [LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity,
    Finset.sum_div] using htail S L n z Δ s hz hΔ hs hlocal hcut

/-- The same weighted tail over an arbitrary terminal subcarrier.  In
particular this applies directly to either side of the square-root terminal
split.  It is strictly stronger than paying `card T * τ L`: after Euler
restoration the bound is just `τ L`, independently of `T.card`. -/
theorem exists_upperRosserBoundaryChains_weightedSubaggregate_uniform_tail
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (nhds 0) ∧
      (∀ L, 0 ≤ τ L) ∧
      ∀ (S : BoundingSieve) (T : Finset ℕ) (L n : ℕ) (z Δ s : ℝ),
        T ⊆ S.prodPrimes.primeFactors →
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        ((∑ q ∈ T,
            (S.nu q / (1 - S.nu q)) *
              ∑ j ∈ Finset.range n,
                LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
                  S.nu (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p))
                  (L + j + N)) *
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤ τ L) := by
  obtain ⟨N, C, hC, hgeom⟩ :=
    exists_upperRosserBoundaryChains_weightedSubaggregate_geometric K hK
  refine ⟨N, (fun L => 90 * C * (9 / 10 : ℝ) ^ L), ?_, ?_, ?_⟩
  · simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (9 / 10 : ℝ)) (by norm_num) (by norm_num)).const_mul (90 * C)
  · intro L
    positivity
  · exact hgeom


end

end MathlibNt.SieveTheory.SwitchingPrinciple
