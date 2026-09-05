import MathlibNt.SieveTheory.UpperRosserSuzukiActualBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- The exact finite upper-Rosser/Suzuki bridge.  The integer `z` exhausts the
finite prime support, while every supported prime lies below the Rosser level.
No local-product hypothesis or approximation occurs in this interface. -/
def UpperRosserSuzukiExactBridge : Prop :=
  ∀ (S : BoundingSieve) (D z : ℕ),
    1 < D →
    (∀ p ∈ S.prodPrimes.primeFactors, p < D) →
    (∀ p ∈ S.prodPrimes.primeFactors, p < z) →
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) ≤
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z

private theorem upper_euler_product_split_at
    (S : BoundingSieve) {q : ℕ} (hq : q ∈ S.prodPrimes.primeFactors) :
    (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      sourceDiscreteEuler S q * (1 - S.nu q) *
        ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          (1 - S.nu p) := by
  classical
  let P := S.prodPrimes.primeFactors
  let L := P.filter (fun p => p < q)
  let U := P.filter (fun p => q < p)
  have hrest : P.filter (fun p => ¬p < q) = insert q U := by
    ext p
    simp only [P, U, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hpP, hpq⟩
      by_cases hpqeq : p = q
      · exact Or.inl hpqeq
      · exact Or.inr ⟨hpP,
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hpq) (fun h => hpqeq h.symm)⟩
    · rintro (rfl | ⟨hpP, hqp⟩)
      · exact ⟨hq, by omega⟩
      · exact ⟨hpP, by omega⟩
  have hqU : q ∉ U := by simp [U]
  calc
    (∏ p ∈ P, (1 - S.nu p)) =
        (∏ p ∈ L, (1 - S.nu p)) *
          ∏ p ∈ P.filter (fun p => ¬p < q), (1 - S.nu p) :=
      (Finset.prod_filter_mul_prod_filter_not P (fun p => p < q)
        (fun p => 1 - S.nu p)).symm
    _ = (∏ p ∈ L, (1 - S.nu p)) *
          ((1 - S.nu q) * ∏ p ∈ U, (1 - S.nu p)) := by
      rw [hrest, Finset.prod_insert hqU]
    _ = sourceDiscreteEuler S q * (1 - S.nu q) *
          ∏ p ∈ P.filter (fun p => q < p), (1 - S.nu p) := by
      unfold sourceDiscreteEuler suzukiSupportedBelow
      ring

private theorem upper_relative_depth_mul_fullEuler
    (S : BoundingSieve) {D q k : ℕ}
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (S.nu q / (1 - S.nu q)) *
        upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k *
        (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)) =
      S.nu q * sourceDiscreteEuler S q *
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdiv : q ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hq |>.2
  have hqfactor : 1 - S.nu q ≠ 0 :=
    ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime q hqprime hqdiv))
  have htailfactor :
      (∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
        (1 - S.nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hpdiv : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpP |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpprime hpdiv))
  unfold upperRosserBoundaryChainsFixedDepthRelativeDensity
  rw [upper_euler_product_split_at S hq]
  field_simp [hqfactor, htailfactor]

private theorem upper_boundary_depth_sum_extend_to_support
    (S : BoundingSieve) (D q : ℕ) :
    (∑ k ∈ Finset.range
        ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1),
      upperRosserBoundaryChainsFixedDepthDensity S.nu D q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) =
      ∑ k ∈ Finset.range (S.prodPrimes.primeFactors.card + 1),
        upperRosserBoundaryChainsFixedDepthDensity S.nu D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) k := by
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact Nat.add_le_add_right
      (Finset.card_le_card (Finset.filter_subset (fun p => q < p)
        S.prodPrimes.primeFactors)) 1
  · intro k hkBig hkSmall
    apply upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
    simp only [Finset.mem_range] at hkBig hkSmall
    omega

/-- Exact equality behind `UpperRosserSuzukiExactBridge`: after restoring the
full Euler product, each relative boundary path becomes its terminal
`nu(q) * sourceDiscreteEuler(q)` times the selected-chain density.  The common
finite depth range is then exactly the odd Suzuki aggregate. -/
theorem mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    (S : BoundingSieve) (D z : ℕ) (hD : 1 < D)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D)
    (hz : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes D) =
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S +
        suzukiActualT S (2 * S.prodPrimes.primeFactors.card + 1) D z := by
  classical
  let P := S.prodPrimes.primeFactors
  let V := ∏ p ∈ P, (1 - S.nu p)
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpdiv : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p (hprime p hp) hpdiv))
  have hV : V ≠ 0 := Finset.prod_ne_zero_iff.mpr hfactor
  have hratio :=
    LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_relativeBoundaryDepths
      S.nu P hD hprime hlevel hfactor
  have hterm (q : ℕ) (hq : q ∈ P) :
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
    calc
      (S.nu q / (1 - S.nu q) *
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
              (P.filter (fun p => q < p)) k) * V =
          ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            (S.nu q / (1 - S.nu q)) *
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k * V := by
            rw [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
            S.nu q * sourceDiscreteEuler S q *
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact upper_relative_depth_mul_fullEuler S hq
      _ = S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k := by
            rw [← Finset.mul_sum,
              upper_boundary_depth_sum_extend_to_support S D q]
  have hdensity :
      LinearSieve.upperRosserSetDensitySum S.nu D P =
        V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
    calc
      LinearSieve.upperRosserSetDensitySum S.nu D P =
          (LinearSieve.upperRosserSetDensitySum S.nu D P / V) * V :=
        (div_mul_cancel₀ _ hV).symm
      _ = (1 + ∑ q ∈ P,
          (S.nu q / (1 - S.nu q)) *
            ∑ k ∈ Finset.range ((P.filter (fun p => q < p)).card + 1),
              upperRosserBoundaryChainsFixedDepthRelativeDensity S.nu D q
                (P.filter (fun p => q < p)) k) * V := by rw [hratio]
      _ = V + ∑ q ∈ P,
          S.nu q * sourceDiscreteEuler S q *
            ∑ k ∈ Finset.range (P.card + 1),
              upperRosserBoundaryChainsFixedDepthDensity S.nu D q
                (P.filter (fun p => q < p)) k := by
        rw [add_mul, one_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        exact hterm q hq
  have hsupport : suzukiSupportedBelow S z = P := by
    ext p
    simp only [suzukiSupportedBelow, P, Finset.mem_filter]
    constructor
    · exact fun hp => hp.1
    · exact fun hp => ⟨hp, hz p hp⟩
  have hboundary :
      (∑ q ∈ P,
        S.nu q * sourceDiscreteEuler S q *
          ∑ k ∈ Finset.range (P.card + 1),
            upperRosserBoundaryChainsFixedDepthDensity S.nu D q
              (P.filter (fun p => q < p)) k) =
        ∑ k ∈ Finset.range (P.card + 1),
          upperSuzukiUnnormalizedLayer S D z k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    unfold upperSuzukiUnnormalizedLayer
    rw [hsupport]
  rw [LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  change LinearSieve.upperRosserSetDensitySum S.nu D P = _
  rw [hdensity, hboundary,
    ← suzukiActualT_odd_eq_sum_upperSuzukiUnnormalizedLayers
      S D z P.card hD]
  simp [P, V, AnalyticNumberTheory.Sieve.sieveProductPrimeFactors]

/-- The finite exact bridge is inhabited unconditionally from the defining
upper-Rosser path expansion and Suzuki's odd-layer identity. -/
theorem upperRosserSuzukiExactBridge : UpperRosserSuzukiExactBridge := by
  intro S D z hD hlevel hz
  exact (mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    S D z hD hlevel hz).le


end MathlibNt.SieveTheory
