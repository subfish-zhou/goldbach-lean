import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserUniformInitialization

/-!
# Honest terminal split for the upper Rosser carrier tail

The terminal carrier is split once, before any estimate is applied.  On the
large-terminal lane, `sqrt (z + 1) ≤ q + 1` gives the initialization power
bound with exponent `2`.  On the complementary lane we sum the already proved
absolute discrete-tail estimate, retaining the exact cardinality payment.

The small-terminal scale conversion is proved below rather than postulated.  Its
fixed-depth proof expands each boundary path exactly, retains the inverse Euler
product over omitted primes, and pays that product by the dimension-one local
product estimate.  The resulting common factor is
`log (z+1) / log (Q+1) * (1 + K / log (Q+1))`; hence the final aggregate keeps
both this `z,Q` growth and the exact filtered-terminal cardinality.  No
continuous tail estimate or carrier-uniform absorption is asserted.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Filter Topology

noncomputable section

/-- The square-root terminal cutoff gives the exponent-two initialization
bound. -/
theorem add_one_le_sq_of_sqrt_le_nat_add_one
    {z : ℝ} {q : ℕ} (hz : 0 ≤ z + 1)
    (hq : Real.sqrt (z + 1) ≤ (q : ℝ) + 1) :
    z + 1 ≤ ((q : ℝ) + 1) ^ (2 : ℝ) := by
  rw [Real.rpow_two]
  rw [← Real.sq_sqrt hz]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hq

/-- Exact carrier partition.  This identity is the bookkeeping boundary used
below; estimates are applied only after this split. -/
theorem sum_terminal_sqrt_split (P : Finset ℕ) (z : ℝ) (f : ℕ → ℝ) :
    (∑ q ∈ P, f q) =
      (∑ q ∈ P.filter (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1), f q) +
      ∑ q ∈ P.filter (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1), f q := by
  simpa using (Finset.sum_filter_add_sum_filter_not P
    (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1) f).symm

/-- Aggregate large-terminal relative block estimate.  The power-bound theorem
is invoked inside one `Finset.sum_le_sum`, and the common geometric envelope is
then counted exactly by the filtered carrier cardinality. -/
theorem exists_upperRosser_largeTerminal_relativeBlock_sum_le_card
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (L n : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        (∀ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1), Q ≤ q) →
        (∑ q ∈ S.prodPrimes.primeFactors.filter
            (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
          ∑ j ∈ Finset.range n,
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              S.nu (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
          (S.prodPrimes.primeFactors.filter
              (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card *
            (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ L) := by
  obtain ⟨Q, hQ, hblock⟩ :=
    exists_upperRosserBoundaryChains_finiteRelativeBlock_geometric K hK
  refine ⟨Q, hQ, ?_⟩
  intro S L n z Δ s hz hΔ hs hlocal hcut hQterm
  let T := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1)
  have hterm : ∀ q ∈ T,
      (∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
        180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ L := by
    intro q hq
    have hqdata := Finset.mem_filter.mp hq
    have hpow : z + 1 ≤ ((q : ℝ) + 1) ^ (2 : ℝ) :=
      add_one_le_sq_of_sqrt_le_nat_add_one (by linarith) hqdata.2
    have h := hblock S L n q z Δ s (hQterm q hq) hz hΔ hs hlocal hcut hqdata.1
    calc
      _ ≤ 90 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ L := h
      _ ≤ 180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ L := by
        have hqPrime := Nat.prime_of_mem_primeFactors hqdata.1
        have hqz : (q : ℝ) ≤ z := hcut q hqdata.1
        have hratio := log_add_one_div_log_nat_add_one_le_of_le_rpow
          hqPrime hqz hpow
        nlinarith [show 0 ≤ (9 / 10 : ℝ) ^ L by positivity]
  calc
    (∑ q ∈ T, ∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
      ∑ q ∈ T, (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ L) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hterm q hq
    _ = T.card * (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ L) := by
      simp

/-- The complementary small-terminal lane is controlled by the existing
**absolute discrete** tail.  Summing is done before simplification, so the cost
is exactly `card small * τ L`, not an untracked per-terminal error. -/
theorem exists_upperRosser_smallTerminal_absoluteBlock_sum_le_card_mul_tail
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (nhds 0) ∧
      ∀ (S : BoundingSieve) (L n : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        (∑ q ∈ S.prodPrimes.primeFactors.filter
            (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
          ∑ j ∈ Finset.range n,
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p))
              (L + j + N)) ≤
          (S.prodPrimes.primeFactors.filter
              (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card * τ L := by
  obtain ⟨N, τ, hτ, htail⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_uniform_tail K hK
  refine ⟨N, τ, hτ, ?_⟩
  intro S L n z Δ s hz hΔ hs hlocal hcut
  let T := S.prodPrimes.primeFactors.filter
    (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1)
  change (∑ q ∈ T, _) ≤ T.card * τ L
  calc
    (∑ q ∈ T, ∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p))
          (L + j + N)) ≤
      ∑ q ∈ T, τ L := by
        apply Finset.sum_le_sum
        intro q hq
        exact htail S L n q z Δ s hz hΔ hs hlocal hcut
          (Finset.mem_filter.mp hq).1
    _ = T.card * τ L := by simp

/-- The remaining scale-conversion interface after the honest split: an
aggregate conversion on the small-terminal lane from the proved absolute
density to the relative Euler-product scale.  It is intentionally not stated
pointwise in `q`; the separate filtered-cardinality payment remains explicit in
the assembly theorem. -/
def UpperRosserSmallTerminalAggregateConversion
    (B : ℝ) (S : BoundingSieve) (L n N : ℕ) (z Δ : ℝ) : Prop :=
  (∑ q ∈ S.prodPrimes.primeFactors.filter
      (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
    ∑ j ∈ Finset.range n,
      LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
        S.nu (Nat.floor Δ + 1) q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j + N)) ≤
    B *
      (∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
        ∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p))
            (L + j + N))

/-- The exact Euler-product payment available once every terminal is at least
`Q`.  Its growth in `z` is retained: for fixed `Q` this is of order `log z`, so
it is not a carrier-uniform constant. -/
noncomputable def upperRosserTerminalEulerConversionFactor
    (K z Q : ℝ) : ℝ :=
  Real.log (z + 1) / Real.log (Q + 1) *
    (1 + K / Real.log (Q + 1))

/-- Fixed-depth conversion from the absolute density with normalized atoms
`ν(p)/(1-ν(p))` to the relative density.  The proof expands each boundary path
exactly: selected primes become normalized atoms, while the genuinely omitted
primes retain their inverse Euler factors.  The dimension-one product estimate
then pays that *whole omitted product once* at the common terminal floor `Q`.
-/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_le_eulerConversionFactor
    {S : BoundingSieve} {K z Q : ℝ} {D q k : ℕ}
    (hQ : 2 ≤ Q) (hQq : Q ≤ q)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
        S.nu D q (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
      upperRosserTerminalEulerConversionFactor K z Q *
        LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
          (fun p => S.nu p / (1 - S.nu p)) D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  classical
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  let A := (P.powerset.filter (LinearSieve.UpperRosserBoundarySet D q)).filter
    (fun u => u.card = 2 * k)
  have hqz : (q : ℝ) ≤ z := hcut q hq
  have hQz : Q + 1 ≤ z + 1 := by linarith
  have hcomplement : ∀ u ∈ A,
      (∏ p ∈ P \ u, (1 - S.nu p)⁻¹) ≤
        upperRosserTerminalEulerConversionFactor K z Q := by
    intro u hu
    have huP : u ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hu).1).1
    apply prod_inv_one_sub_nu_le_of_subset_interval hlocal
        (z₁ := Q + 1) (z₂ := z + 1)
    · linarith
    · exact hQz
    · intro p hp
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
    · intro p hp
      have hpP := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
      constructor
      · have hqp : (q : ℝ) + 1 ≤ p := by
          exact_mod_cast Nat.add_one_le_iff.mpr hpP.2
        linarith
      · linarith [hcut p hpP.1]
  have hatom_nonneg : ∀ u ∈ A,
      0 ≤ ∏ p ∈ u, S.nu p / (1 - S.nu p) := by
    intro u hu
    apply Finset.prod_nonneg
    intro p hp
    have huP : u ⊆ P :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp
        (Finset.mem_filter.mp hu).1).1
    exact nu_div_one_sub_nonneg_of_mem
      (Finset.mem_filter.mp (huP hp)).1
  unfold LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
  rw [LinearSieve.sum_upperRosserBoundaryChains_fixed_length,
    LinearSieve.sum_upperRosserBoundaryChains_fixed_length]
  change (∑ u ∈ A, ∏ p ∈ u, S.nu p) / ∏ p ∈ P, (1 - S.nu p) ≤ _
  rw [Finset.sum_div]
  calc
    (∑ u ∈ A, (∏ p ∈ u, S.nu p) / ∏ p ∈ P, (1 - S.nu p)) =
        ∑ u ∈ A,
          (∏ p ∈ u, S.nu p / (1 - S.nu p)) *
            ∏ p ∈ P \ u, (1 - S.nu p)⁻¹ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact LinearSieve.prod_nu_div_eulerProduct_eq S.nu
        (Finset.mem_powerset.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hu).1).1)
    _ ≤ ∑ u ∈ A,
        (∏ p ∈ u, S.nu p / (1 - S.nu p)) *
          upperRosserTerminalEulerConversionFactor K z Q := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hcomplement u hu) (hatom_nonneg u hu)
    _ = upperRosserTerminalEulerConversionFactor K z Q *
        ∑ u ∈ A, ∏ p ∈ u, S.nu p / (1 - S.nu p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Genuine aggregate producer for the frozen small-terminal conversion
interface.  Unlike a postulated uniform `B`, the factor keeps the initialization
Euler denominator visible through `B(z,Q)`.  The square-root condition identifies
the lane but is not used to erase this growth. -/
theorem upperRosserSmallTerminalAggregateConversion_of_terminalFloor
    {K Q : ℝ} (hQ : 2 ≤ Q) {S : BoundingSieve} {L n N : ℕ} {z Δ : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hQsmall : ∀ q ∈ S.prodPrimes.primeFactors.filter
      (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1), Q ≤ q) :
    UpperRosserSmallTerminalAggregateConversion
      (upperRosserTerminalEulerConversionFactor K z Q) S L n N z Δ := by
  unfold UpperRosserSmallTerminalAggregateConversion
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact upperRosserBoundaryChainsFixedDepthRelativeDensity_le_eulerConversionFactor
    hQ (hQsmall q hq) hlocal hcut (Finset.mem_filter.mp hq).1

/-- Every terminal in the prime carrier is at least two.  Consequently the
small-terminal aggregate always has the explicit factor `B(z,2)`, with no
extra terminal-floor premise. -/
theorem upperRosserSmallTerminalAggregateConversion_two
    {K : ℝ} {S : BoundingSieve} {L n N : ℕ} {z Δ : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) :
    UpperRosserSmallTerminalAggregateConversion
      (upperRosserTerminalEulerConversionFactor K z 2) S L n N z Δ := by
  apply upperRosserSmallTerminalAggregateConversion_of_terminalFloor
    (K := K) (Q := 2) (by norm_num) hlocal hcut
  intro q hq
  exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).two_le

/-- Conditional unified relative carrier-tail inequality.  The proof first
rewrites the whole carrier sum by the exact terminal partition, then inserts
the aggregate large- and small-lane bounds.  The scale mismatch is isolated in
`UpperRosserSmallTerminalAggregateConversion`; the cardinality factors are not
silently discarded. -/
theorem upperRosser_terminalSplit_unifiedRelativeCarrierTail
    {B : ℝ} (hB : 0 ≤ B) {S : BoundingSieve} {L n N : ℕ} {z Δ τ : ℝ}
    (hlarge :
      (∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
        ∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j + N)) ≤
        (S.prodPrimes.primeFactors.filter
            (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card *
          (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ (L + N)))
    (hsmallAbs :
      (∑ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1),
        ∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p))
            (L + j + N)) ≤
        (S.prodPrimes.primeFactors.filter
            (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card * τ)
    (hconvert : UpperRosserSmallTerminalAggregateConversion B S L n N z Δ) :
    (∑ q ∈ S.prodPrimes.primeFactors,
      ∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j + N)) ≤
      (S.prodPrimes.primeFactors.filter
          (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card *
        (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ (L + N)) +
      B * ((S.prodPrimes.primeFactors.filter
          (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card * τ) := by
  rw [sum_terminal_sqrt_split]
  exact add_le_add hlarge (hconvert.trans (mul_le_mul_of_nonneg_left hsmallAbs hB))

/-- Strongest unconditional terminal-split consumer currently available.  The
small lane is geometric in `L`, but its exact coefficient is

`B(z,2) * card(small terminals)`.

Thus the Euler denominator and terminal cardinality are both paid explicitly;
this statement deliberately does not promote the result to a cutoff uniform in
the varying sieve and endpoint. -/
theorem exists_upperRosser_terminalSplit_relativeCarrierTail_explicit
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, ∃ N : ℕ, ∃ τ : ℕ → ℝ,
      2 ≤ Q ∧ Tendsto τ atTop (nhds 0) ∧
      ∀ (S : BoundingSieve) (L n : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        (∀ q ∈ S.prodPrimes.primeFactors.filter
          (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1), Q ≤ q) →
        (∑ q ∈ S.prodPrimes.primeFactors,
          ∑ j ∈ Finset.range n,
            LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
              S.nu (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p))
              (L + j + N)) ≤
          (S.prodPrimes.primeFactors.filter
              (fun q : ℕ => Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card *
            (180 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ (L + N)) +
          upperRosserTerminalEulerConversionFactor K z 2 *
            ((S.prodPrimes.primeFactors.filter
              (fun q : ℕ => ¬ Real.sqrt (z + 1) ≤ (q : ℝ) + 1)).card * τ L) := by
  obtain ⟨Q, hQ, hlarge⟩ :=
    exists_upperRosser_largeTerminal_relativeBlock_sum_le_card K hK
  obtain ⟨N, τ, hτ, hsmall⟩ :=
    exists_upperRosser_smallTerminal_absoluteBlock_sum_le_card_mul_tail K hK
  refine ⟨Q, N, τ, hQ, hτ, ?_⟩
  intro S L n z Δ s hz hΔ hs hlocal hcut hQterm
  have hB : 0 ≤ upperRosserTerminalEulerConversionFactor K z 2 := by
    unfold upperRosserTerminalEulerConversionFactor
    have hlogz : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
    have hlogthree : 0 < Real.log (2 + 1 : ℝ) := Real.log_pos (by norm_num)
    positivity
  exact upperRosser_terminalSplit_unifiedRelativeCarrierTail
    (B := upperRosserTerminalEulerConversionFactor K z 2)
    (S := S) (L := L) (n := n) (N := N) (z := z) (Δ := Δ) (τ := τ L) hB
    (by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hlarge S (L + N) n z Δ s hz hΔ hs hlocal hcut hQterm)
    (hsmall S L n z Δ s hz hΔ hs hlocal hcut)
    (upperRosserSmallTerminalAggregateConversion_two hlocal hcut)


end

end MathlibNt.SieveTheory.SwitchingPrinciple
