import MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeCoefficients
import MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeSmall
import MathlibNt.SieveTheory.UpperRosserSuzukiExactBridge
import MathlibNt.SieveTheory.SuzukiLiteralAllDepthLowerRosserExact

/-!
# The original small weights and the admitted finite Suzuki producers

Strict real-level tests become tests at the natural ceiling. Deleting
zero-density primes preserves the entire signed densities and the Euler
product. The lower and upper defects are exactly the actual Suzuki sums
at exhaustive even and odd depths, respectively.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open ArithmeticFunction Finset SwitchingPrinciple
open scoped Classical

theorem lowerAdmissibleSet_iff_producer (L : ℝ) (s : Finset ℕ) :
    LowerAdmissibleSet L s ↔ LinearSieve.LowerRosserAdmissibleSet ⌈L⌉₊ s :=
  lowerAdmissibleSet_iff_natCeil L s

theorem upperAdmissibleSet_iff_producer (L : ℝ) (s : Finset ℕ) :
    UpperAdmissibleSet L s ↔ LinearSieve.UpperRosserAdmissibleSet ⌈L⌉₊ s :=
  upperAdmissibleSet_iff_natCeil L s

theorem setWeight_eq_producer (L : ℝ) (s : Finset ℕ) :
    setWeight L s = LinearSieve.lowerRosserSetWeight ⌈L⌉₊ s := by
  rw [setWeight_eq_natCeil_tests]
  unfold LinearSieve.lowerRosserSetWeight LinearSieve.LowerRosserAdmissibleSet
  split_ifs <;> rfl

theorem upperSetWeight_eq_producer (L : ℝ) (s : Finset ℕ) :
    upperSetWeight L s = LinearSieve.upperRosserSetWeight ⌈L⌉₊ s := by
  rw [upperSetWeight_eq_natCeil_tests]
  unfold LinearSieve.upperRosserSetWeight LinearSieve.UpperRosserAdmissibleSet
  split_ifs <;> rfl

theorem lowerSetDensity_eq_producer (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) :
    lowerSetDensity L g B = LinearSieve.lowerRosserSetDensitySum g ⌈L⌉₊ B := by
  simp only [lowerSetDensity, LinearSieve.lowerRosserSetDensitySum, setWeight_eq_producer]

theorem upperSetDensity_eq_producer (L : ℝ) (g : ℕ → ℝ) (B : Finset ℕ) :
    upperSetDensity L g B = LinearSieve.upperRosserSetDensitySum g ⌈L⌉₊ B := by
  simp only [upperSetDensity, LinearSieve.upperRosserSetDensitySum, upperSetWeight_eq_producer]

variable (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
  (g : ArithmeticFunction ℝ) (hgm : g.IsMultiplicative)
  (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1)

theorem densityBoundingSieve_actual_mainSums (L : ℝ) :
    let S := densityBoundingSieve B hB g hgm hg
    S.mainSum (LinearSieve.lowerRosserWeight S.prodPrimes ⌈L⌉₊) =
        lowerSetDensity L g B ∧
    S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes ⌈L⌉₊) =
        upperSetDensity L g B := by
  simpa only [lowerWeight_ceil, upperWeight_ceil,
    lowerWeight_eq_producer, upperWeight_eq_producer] using
      densityBoundingSieve_mainSums_eq_setDensities B hB g hgm hg L

theorem densityBoundingSieve_supportedBelow {u : ℝ}
    (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    suzukiSupportedBelow (densityBoundingSieve B hB g hgm hg) ⌈u⌉₊ =
      nonzeroDensityPrimes B g := by
  unfold suzukiSupportedBelow
  rw [Finset.filter_eq_self.mpr
    (densityBoundingSieve_prime_lt_ceil B hB g hgm hg hcut),
    densityBoundingSieve_primeFactors]

theorem densityBoundingSieve_hasDimensionOneLocalProductBound {K : ℝ}
    (hK : 0 ≤ K) (hdim : DimensionOneProductBound B g K) :
    HasDimensionOneLocalProductBound (densityBoundingSieve B hB g hgm hg) K :=
  densityBoundingSieve_localProduct B hB g hgm hg hK hdim

theorem densityBoundingSieve_suzukiVProduct {u : ℝ}
    (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    suzukiVProduct (densityBoundingSieve B hB g hgm hg) (⌈u⌉₊ : ℝ) =
      ∏ p ∈ B, (1 - g p) := by
  unfold suzukiVProduct
  rw [Finset.filter_eq_self.mpr (fun p hp =>
    (Nat.cast_lt (α := ℝ)).mpr
      (densityBoundingSieve_prime_lt_ceil B hB g hgm hg hcut p hp))]
  exact densityBoundingSieve_euler B hB g hgm hg

/-- The lower depth is even and its sum is subtracted; the upper depth is
odd and its sum is added. Both exhaust the zero-deleted finite carrier. -/
theorem densityBoundingSieve_actual_densities {L u : ℝ}
    (hL : 1 < L) (huL : u ≤ L) (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    let S := densityBoundingSieve B hB g hgm hg
    let T := nonzeroDensityPrimes B g
    lowerSetDensity L g B = (∏ p ∈ B, (1 - g p)) -
        suzukiActualT S (2 * (T.card + 1)) ⌈L⌉₊ ⌈u⌉₊ ∧
    upperSetDensity L g B = (∏ p ∈ B, (1 - g p)) +
        suzukiActualT S (2 * T.card + 1) ⌈L⌉₊ ⌈u⌉₊ := by
  let S := densityBoundingSieve B hB g hgm hg
  have hR : 1 < ⌈L⌉₊ := Nat.lt_ceil.mpr (by simpa using hL)
  have hzR : ⌈u⌉₊ ≤ ⌈L⌉₊ := Nat.ceil_mono huL
  have hcarrier : suzukiSupportedBelow S ⌈u⌉₊ = nonzeroDensityPrimes B g :=
    densityBoundingSieve_supportedBelow B hB g hgm hg hcut
  have hEuler : sourceDiscreteEuler S ⌈u⌉₊ = ∏ p ∈ B, (1 - g p) := by
    unfold sourceDiscreteEuler
    rw [hcarrier]
    exact eulerProduct_delete_zero B g
  have hloset :
      LinearSieve.lowerRosserSetDensitySum S.nu ⌈L⌉₊
          (suzukiSupportedBelow S ⌈u⌉₊) = lowerSetDensity L g B := by
    rw [hcarrier]
    change LinearSieve.lowerRosserSetDensitySum g ⌈L⌉₊
      (nonzeroDensityPrimes B g) = _
    rw [← lowerSetDensity_eq_producer, lowerSetDensity_delete_zero]
  have hlo := lowerRosserSetDensitySum_eq_euler_sub_suzukiActualT_all_supported
    S hR hzR
  rw [hloset, hEuler, hcarrier] at hlo
  have hup := mainSum_upperRosserWeight_eq_sieveProduct_add_suzukiActualT
    S ⌈L⌉₊ ⌈u⌉₊ hR
      (densityBoundingSieve_prime_lt_ceil B hB g hgm hg
        (fun p hp => (hcut p hp).trans_le huL))
      (densityBoundingSieve_prime_lt_ceil B hB g hgm hg hcut)
  have hsum : S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes ⌈L⌉₊) =
      upperSetDensity L g B :=
    (densityBoundingSieve_actual_mainSums B hB g hgm hg L).2
  have hEulerFull : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S =
      ∏ p ∈ B, (1 - g p) :=
    densityBoundingSieve_euler B hB g hgm hg
  rw [hsum, hEulerFull] at hup
  have hpf : S.prodPrimes.primeFactors = nonzeroDensityPrimes B g :=
    densityBoundingSieve_primeFactors B hB g hgm hg
  rw [hpf] at hup
  exact ⟨hlo, hup⟩

/-- Exact identification of the whole original boundary defects, not just
their high-minimum-prime contributions. -/
theorem densityDefects_eq_suzukiActualT {L u : ℝ}
    (hL : 1 < L) (huL : u ≤ L) (hcut : ∀ p ∈ B, (p : ℝ) < u) :
    let S := densityBoundingSieve B hB g hgm hg
    let T := nonzeroDensityPrimes B g
    lowerDensityDefect L g (B.sort (· ≤ ·)) =
        suzukiActualT S (2 * (T.card + 1)) ⌈L⌉₊ ⌈u⌉₊ ∧
    upperDensityDefect L g (B.sort (· ≤ ·)) =
        suzukiActualT S (2 * T.card + 1) ⌈L⌉₊ ⌈u⌉₊ := by
  have hsource := densityBoundingSieve_actual_densities B hB g hgm hg hL huL hcut
  have hlo := lowerSetDensity_eq_euler_sub_defect g hL (B.sort (· ≤ ·))
    (B.sort_nodup _) (B.pairwise_sort _)
    (fun p hp => hB p (by simpa using hp))
    (fun p hp => (hcut p (by simpa using hp)).trans_le huL)
  have hup := upperSetDensity_eq_euler_add_defect g hL (B.sort (· ≤ ·))
    (B.sort_nodup _) (B.pairwise_sort _)
    (fun p hp => hB p (by simpa using hp))
  simp only [Finset.sort_toFinset] at hlo hup
  dsimp only at hsource ⊢
  constructor
  · linarith [hsource.1]
  · linarith [hsource.2]

theorem smallDensityBoundingSieve_hasDimensionOneLocalProductBound
    (P : Finset ℕ) (D ε : ℝ) (g : ArithmeticFunction ℝ)
    (hgm : g.IsMultiplicative)
    (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1)
    {K : ℝ} (hK : 0 ≤ K) (hdim : DimensionOneProductBound P g K) :
    HasDimensionOneLocalProductBound (smallDensityBoundingSieve P D ε g hgm hg) K :=
  smallDensityBoundingSieve_localProduct P D ε g hgm hg hK hdim

theorem smallDensityDefects_eq_suzukiActualT
    (P : Finset ℕ) {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (g : ArithmeticFunction ℝ) (hgm : g.IsMultiplicative)
    (hg : ∀ p ∈ geometricSmallPrimes P D ε, 0 ≤ g p ∧ g p < 1) :
    let B := geometricSmallPrimes P D ε
    let S := smallDensityBoundingSieve P D ε g hgm hg
    let T := nonzeroDensityPrimes B g
    lowerDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) =
        suzukiActualT S (2 * (T.card + 1)) ⌈D ^ ε⌉₊ ⌈D ^ (ε ^ 2)⌉₊ ∧
    upperDensityDefect (D ^ ε) g (B.sort (· ≤ ·)) =
        suzukiActualT S (2 * T.card + 1) ⌈D ^ ε⌉₊ ⌈D ^ (ε ^ 2)⌉₊ := by
  exact densityDefects_eq_suzukiActualT (geometricSmallPrimes P D ε)
    (smallPrimes_prime P D ε) g hgm hg
    (Real.one_lt_rpow (by linarith) hε)
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith))
    (fun p hp => (Finset.mem_filter.mp hp).2.2)

#check densityDefects_eq_suzukiActualT
#print axioms lowerWeight_eq_producer
#print axioms upperWeight_eq_producer
#print axioms densityBoundingSieve_hasDimensionOneLocalProductBound
#print axioms densityDefects_eq_suzukiActualT
#print axioms smallDensityDefects_eq_suzukiActualT

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
