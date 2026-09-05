import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrence
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve
import MathlibNt.SieveTheory.LinearSieve.Rosser.LowerRosserBoundaryNonneg

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144Equation1410

/-- The genuine depth-two lower-Rosser boundary mass, written with the largest
stored prime `p` first and the external terminal prime `q` second.  The factor
`sourceDiscreteEuler S q` is the product of all Euler factors below `q`; it is
exactly the factor acquired when the density recurrence reaches terminal `q`. -/
noncomputable def lowerRosserDepthTwoSourceMass
    (S : BoundingSieve) (D z : ℕ) : ℝ :=
  ∑ p ∈ suzukiSupportedBelow S z,
    S.nu p * ∑ q ∈ (suzukiSupportedBelow S p).filter
        (fun q => p < D ∧ D ≤ p * q ^ 3),
      S.nu q * sourceDiscreteEuler S q

/-- In the legal even depth-two range `z² ≤ D`, Suzuki's actual source layer is
exactly the singleton lower-Rosser boundary carrier.  Outside this range the
predicates are not equivalent: the lower carrier has `p < D`, whereas the
source recursion has the divided-level terminal test. -/
theorem suzukiSourceV_two_eq_lowerRosserDepthTwoSourceMass
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 2 ≤ D) :
    suzukiSourceV S 2 D z = lowerRosserDepthTwoSourceMass S D z := by
  classical
  rw [show suzukiSourceV S 2 D z =
      ∑ p ∈ suzukiSourceOuterCarrier 2 D z S.prodPrimes.primeFactors,
        S.nu p *
          ∑ q ∈ (suzukiSupportedBelow S p).filter
              (fun q => D ⌈/⌉ p ≤ q ^ 3),
            S.nu q * sourceDiscreteEuler S q by rfl]
  unfold lowerRosserDepthTwoSourceMass suzukiSourceOuterCarrier
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hpz : p < z := (Finset.mem_filter.mp hp).2
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hp).1
  have hp0 : 0 < p := hpprime.pos
  have hpD : p < D := by
    have hp2lt : p < p ^ 2 := by
      have hp2 : 2 ≤ p := hpprime.two_le
      nlinarith
    have hp2z2 : p ^ 2 < z ^ 2 := Nat.pow_lt_pow_left hpz (by norm_num)
    omega
  by_cases houter : D ≤ p ^ 4
  · simp only [houter, true_and]
    apply congrArg (fun x : ℝ => S.nu p * x)
    apply Finset.sum_congr
    · ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq, hceil⟩
        exact ⟨hq, hpD, (ceilDiv_le_iff_le_mul hp0).1 hceil⟩
      · rintro ⟨hq, _, hterminal⟩
        exact ⟨hq, (ceilDiv_le_iff_le_mul hp0).2 hterminal⟩
    · intro q hq
      rfl
  · simp only [houter, false_and, if_false]
    symm
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro q hq
    exfalso
    have hqmem := Finset.mem_filter.mp hq
    have hqz : q < p := (Finset.mem_filter.mp hqmem.1).2
    have hqp3 : p * q ^ 3 < p ^ 4 := by
      have hq3 : q ^ 3 < p ^ 3 := Nat.pow_lt_pow_left hqz (by norm_num)
      have := Nat.mul_lt_mul_of_pos_left hq3 hp0
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    exact houter (hqmem.2.2.trans hqp3.le)

/-- Iterating the one-prime recurrence expands the lower density as the full
Euler product minus an explicit recursively weighted sum of odd cubic boundary
layers.  The list is increasing, so its head is the least prime inserted last. -/
theorem lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum
    (S : BoundingSieve) {D z : ℕ} (qs : List ℕ)
    (hcarrier : qs.toFinset = suzukiSupportedBelow S z)
    (hprime : ∀ q ∈ qs, q.Prime) (hD : ∀ q ∈ qs, q < D)
    (hordered : qs.Pairwise (· < ·)) (hD1 : 1 < D) :
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) =
      sourceDiscreteEuler S z -
        lowerRosserBoundaryAccum S.nu D (∅ : Finset ℕ) qs := by
  have hfoldAll : ∀ ls : List ℕ, ls.foldr insert ∅ = ls.toFinset := by
    intro ls
    induction ls with
    | nil => simp
    | cons q ls ih => simp [ih]
  have hfold := hfoldAll qs
  have hiter := lowerRosserSetDensitySum_foldr_insert
    S.nu D (∅ : Finset ℕ) qs hprime hD hordered (by simp) (by simp)
  rw [hfold, hcarrier] at hiter
  have hbase : lowerRosserSetDensitySum S.nu D ∅ = 1 := by
    have hrel := lowerRosserSetRelativeDensity_empty S.nu hD1
    simpa [lowerRosserSetRelativeDensity] using hrel
  have hprod : (qs.map (fun q => 1 - S.nu q)).prod =
      sourceDiscreteEuler S z := by
    rw [← List.prod_toFinset (fun q => 1 - S.nu q) hordered.nodup,
      hcarrier]
    rfl
  rw [hbase, hprod, mul_one] at hiter
  exact hiter

/-- The deep discrepancy on an ordered prime carrier.  Unlike the old opaque
`Euler - density - V₂` difference, this is the explicit all-boundary
accumulator with the concrete depth-two source carrier removed. -/
noncomputable def lowerRosserDeepBoundaryTail
    (S : BoundingSieve) (D z : ℕ) (qs : List ℕ) : ℝ :=
  lowerRosserBoundaryAccum S.nu D (∅ : Finset ℕ) qs -
    lowerRosserDepthTwoSourceMass S D z

/-- The genuine depth-two source mass is nonnegative. -/
theorem lowerRosserDepthTwoSourceMass_nonneg
    (S : BoundingSieve) (D z : ℕ) :
    0 ≤ lowerRosserDepthTwoSourceMass S D z := by
  unfold lowerRosserDepthTwoSourceMass
  apply Finset.sum_nonneg
  intro p hp
  have hpP : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
  have hpnu : 0 ≤ S.nu p :=
    (S.nu_pos_of_prime p hpprime (Nat.dvd_of_mem_primeFactors hpP)).le
  apply mul_nonneg hpnu
  apply Finset.sum_nonneg
  intro q hq
  have hqP : q ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqP
  have hqnu : 0 ≤ S.nu q :=
    (S.nu_pos_of_prime q hqprime (Nat.dvd_of_mem_primeFactors hqP)).le
  apply mul_nonneg hqnu
  unfold sourceDiscreteEuler
  apply Finset.prod_nonneg
  intro r hr
  have hrP : r ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp hr).1
  have hrprime : r.Prime := Nat.prime_of_mem_primeFactors hrP
  exact sub_nonneg.mpr
    (S.nu_lt_one_of_prime r hrprime
      (Nat.dvd_of_mem_primeFactors hrP)).le

/-- The explicit deep tail has a quantitative one-sided enclosure: it is at
most the total boundary loss and at least minus the depth-two source mass. -/
theorem lowerRosserDeepBoundaryTail_bounds
    (S : BoundingSieve) {D z : ℕ} (qs : List ℕ)
    (hfold : qs.foldr insert (∅ : Finset ℕ) = suzukiSupportedBelow S z) :
    -lowerRosserDepthTwoSourceMass S D z ≤
        lowerRosserDeepBoundaryTail S D z qs ∧
      lowerRosserDeepBoundaryTail S D z qs ≤
        lowerRosserBoundaryAccum S.nu D (∅ : Finset ℕ) qs := by
  have hnu : ∀ p ∈ qs.foldr insert (∅ : Finset ℕ), 0 ≤ S.nu p := by
    intro p hp
    rw [hfold] at hp
    have hpP : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp).1
    exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.dvd_of_mem_primeFactors hpP)).le
  have hnuOne : ∀ p ∈ qs.foldr insert (∅ : Finset ℕ), S.nu p ≤ 1 := by
    intro p hp
    rw [hfold] at hp
    have hpP : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp).1
    exact (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpP)
      (Nat.dvd_of_mem_primeFactors hpP)).le
  have hacc := lowerRosserBoundaryAccum_nonneg S.nu D (∅ : Finset ℕ) qs hnu hnuOne
  have htwo := lowerRosserDepthTwoSourceMass_nonneg S D z
  unfold lowerRosserDeepBoundaryTail
  constructor <;> linarith

/-- A JR-ready lower estimate with no absolute value: any explicit upper bound
for the recursive boundary accumulator immediately gives a lower density bound. -/
theorem lowerRosserSetDensitySum_lower_of_boundaryAccum_le
    (S : BoundingSieve) {D z : ℕ} (qs : List ℕ)
    (hcarrier : qs.toFinset = suzukiSupportedBelow S z)
    (hprime : ∀ q ∈ qs, q.Prime) (hD : ∀ q ∈ qs, q < D)
    (hordered : qs.Pairwise (· < ·)) (hD1 : 1 < D)
    {B : ℝ} (hB : lowerRosserBoundaryAccum S.nu D (∅ : Finset ℕ) qs ≤ B) :
    sourceDiscreteEuler S z - B ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  rw [lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum S qs hcarrier
    hprime hD hordered hD1]
  linarith

/-- The concrete discrepancy left after transporting the genuine depth-two
source layer into the full lower-Rosser density.  It includes every deeper
boundary layer and any out-of-range carrier discrepancy; it is data, not an
abstract proposition. -/
noncomputable def lowerRosserDensityDiscrepancy
    (S : BoundingSieve) (D z : ℕ) : ℝ :=
  sourceDiscreteEuler S z -
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) -
    suzukiActualT S 2 D z

/-- On any ordered enumeration of the supported primes, the source-to-density
 discrepancy is exactly the explicit deeper boundary tail. -/
theorem lowerRosserDensityDiscrepancy_eq_deepBoundaryTail
    (S : BoundingSieve) {D z : ℕ} (qs : List ℕ)
    (hcarrier : qs.toFinset = suzukiSupportedBelow S z)
    (hprime : ∀ q ∈ qs, q.Prime) (hD : ∀ q ∈ qs, q < D)
    (hordered : qs.Pairwise (· < ·)) (hD1 : 1 < D)
    (hzD : z ^ 2 ≤ D) :
    lowerRosserDensityDiscrepancy S D z =
      lowerRosserDeepBoundaryTail S D z qs := by
  rw [lowerRosserDensityDiscrepancy, lowerRosserDeepBoundaryTail,
    lowerRosserSetDensitySum_eq_euler_sub_boundaryAccum S qs hcarrier
      hprime hD hordered hD1,
    show suzukiActualT S 2 D z = lowerRosserDepthTwoSourceMass S D z by
      simpa [suzukiActualT] using
        suzukiSourceV_two_eq_lowerRosserDepthTwoSourceMass S hzD]
  ring

/-- Exact source-to-density decomposition.  In particular, replacing the
boundary carrier by `suzukiActualT` without this discrepancy is unjustified. -/
theorem lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_two_sub_discrepancy
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) =
      sourceDiscreteEuler S z - suzukiActualT S 2 D z -
        lowerRosserDensityDiscrepancy S D z := by
  unfold lowerRosserDensityDiscrepancy
  ring

/-- Unconditional honest lower transport: the unknown deeper/discrepant tail is
paid for by its absolute value rather than silently set to zero. -/
theorem lowerRosserSetDensitySum_lower_transport_two
    (S : BoundingSieve) (D z : ℕ) :
    sourceDiscreteEuler S z - suzukiActualT S 2 D z -
        |lowerRosserDensityDiscrepancy S D z| ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  rw [lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_two_sub_discrepancy]
  linarith [le_abs_self (lowerRosserDensityDiscrepancy S D z)]

/-- In the legal even depth-two range, the preceding inequality visibly uses
the real lower-boundary carrier, not a falsely identified predicate. -/
theorem lowerRosserSetDensitySum_lower_transport_depthTwoCarrier
    (S : BoundingSieve) {D z : ℕ} (hzD : z ^ 2 ≤ D) :
    sourceDiscreteEuler S z - lowerRosserDepthTwoSourceMass S D z -
        |lowerRosserDensityDiscrepancy S D z| ≤
      lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) := by
  have hV := suzukiSourceV_two_eq_lowerRosserDepthTwoSourceMass S hzD
  simpa [suzukiActualT, hV] using
    lowerRosserSetDensitySum_lower_transport_two S D z


end MathlibNt.SieveTheory
