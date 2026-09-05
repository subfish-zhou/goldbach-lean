import MathlibNt.SieveTheory.LinearSieve.Rosser.LowerRosserSuzukiActualBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVOneNaturalBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple

/-- An exact pair-depth slice vanishes once the pair-depth itself exceeds the
finite stored-prime carrier.  This intentionally weak cutoff is enough to put
all terminal-prime slices over one common finite range. -/
private theorem lowerRosserBoundaryChainsFixedPairDepth0Density_eq_zero_of_card_lt
    (nu : ℕ → ℝ) {D q k : ℕ} {P : Finset ℕ}
    (hqP : q ∉ P) (hqprime : q.Prime) (hqmin : ∀ p ∈ P, q ≤ p)
    (hk : P.card < k) :
    lowerRosserBoundaryChainsFixedPairDepth0Density nu D q P k = 0 := by
  classical
  unfold lowerRosserBoundaryChainsFixedPairDepth0Density
  apply Finset.sum_eq_zero
  intro l hl
  have hl' := Finset.mem_filter.mp hl
  have hnodup : l.Nodup :=
    (mem_lowerRosserBoundaryChains_iff hqP hqprime hqmin).mp hl'.1 |>.1
  have hlsub : l.toFinset ⊆ P := by
    unfold lowerRosserBoundaryChains at hl'
    obtain ⟨s, hs, hsort⟩ := Finset.mem_image.mp hl'.1
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    simpa [← hsort] using hsub
  have hlenle : l.length ≤ P.card := by
    rw [← List.toFinset_card_of_nodup hnodup]
    exact Finset.card_le_card hlsub
  omega

/-- The powerset boundary at every supported terminal prime may be summed over
one common finite pair-depth range. -/
private theorem lowerRosserBoundaryMass_eq_sum_commonPairDepth
    (S : BoundingSieve) {D z q : ℕ} (hq : q ∈ suzukiSupportedBelow S z) :
    lowerRosserBoundaryMass S.nu D q
        ((suzukiSupportedBelow S z).filter (fun p => q < p)) =
      ∑ k ∈ Finset.range ((suzukiSupportedBelow S z).card + 1),
        lowerSuzukiDiscreteKernel S D z k q := by
  classical
  let P := (suzukiSupportedBelow S z).filter (fun p => q < p)
  have hqprime : q.Prime :=
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hqP : q ∉ P := by simp [P]
  have hqmin : ∀ p ∈ P, q ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.le
  rw [lowerRosserBoundaryMass_eq_sum_fixedPairDepth0Density
    S.nu hqP hqprime hqmin]
  have hsub : P ⊆ suzukiSupportedBelow S z := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hcard : P.card + 1 ≤ (suzukiSupportedBelow S z).card + 1 := by
    exact Nat.succ_le_succ (Finset.card_le_card hsub)
  apply Finset.sum_subset (Finset.range_mono hcard)
  intro k hkGlobal hkLocal
  have hklt : P.card < k := by
    simp only [Finset.mem_range] at hkGlobal hkLocal
    omega
  change lowerSuzukiDiscreteKernel S D z k q = 0
  unfold lowerSuzukiDiscreteKernel
  exact lowerRosserBoundaryChainsFixedPairDepth0Density_eq_zero_of_card_lt
    S.nu hqP hqprime hqmin hklt

/-- The canonical lower-Rosser accumulator is exactly the finite sum of every
unnormalized Suzuki pair-depth layer.  There is no analytic or truncation
premise: `card + 1` is a complete finite-support cutoff. -/
theorem lowerRosserBoundaryAccum_supportedBelow_eq_sum_unnormalizedLayers
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserBoundaryAccum S.nu D ∅ (suzukiSupportedBelowList S z) =
      ∑ k ∈ Finset.range ((suzukiSupportedBelow S z).card + 1),
        lowerSuzukiUnnormalizedLayer S D z k := by
  classical
  rw [lowerRosserBoundaryAccum_supportedBelow_eq_primeSum]
  calc
    (∑ q ∈ suzukiSupportedBelow S z,
        S.nu q * sourceDiscreteEuler S q *
          lowerRosserBoundaryMass S.nu D q
            ((suzukiSupportedBelow S z).filter (fun r => q < r))) =
      ∑ q ∈ suzukiSupportedBelow S z,
        S.nu q * sourceDiscreteEuler S q *
          (∑ k ∈ Finset.range ((suzukiSupportedBelow S z).card + 1),
            lowerSuzukiDiscreteKernel S D z k q) := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [lowerRosserBoundaryMass_eq_sum_commonPairDepth S hq]
    _ = ∑ k ∈ Finset.range ((suzukiSupportedBelow S z).card + 1),
          lowerSuzukiUnnormalizedLayer S D z k := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            unfold lowerSuzukiUnnormalizedLayer
            rfl

/-- The exact terminal-factor identity.  Multiplication by the full Euler
product converts the normalized suffix ratio into the Euler product strictly
below the terminal prime. -/
theorem sourceDiscreteEuler_mul_suzukiSuffixRatio
    (S : BoundingSieve) {z q : ℕ} (hq : q ∈ suzukiSupportedBelow S z) :
    sourceDiscreteEuler S z * suzukiSuffixRatio S z q =
      sourceDiscreteEuler S q := by
  have hqz : q < z := (Finset.mem_filter.mp hq).2
  have hreal := suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S
    (show (q : ℝ) < (z : ℝ) by exact_mod_cast hqz)
  have hVz : suzukiVProduct S (z : ℝ) = sourceDiscreteEuler S z := by
    unfold suzukiVProduct sourceDiscreteEuler suzukiSupportedBelow
    congr 1
    ext p
    simp
  have hratio : suzukiLocalRatio S (q : ℝ) (z : ℝ) =
      suzukiSuffixRatio S z q := by
    rw [suzukiLocalRatio_nat_right S z (by positivity : (0 : ℝ) ≤ (q : ℝ))]
    norm_num
  simpa [hVz, hratio] using hreal

/-- Exact normalization of each pair-depth layer.  The coefficient is the full
finite Euler product `sourceDiscreteEuler S z`; no suffix ratio is substituted
for the accumulator's terminal factor. -/
theorem lowerSuzukiUnnormalizedLayer_eq_euler_mul_normalizedLayer
    (S : BoundingSieve) (D z k : ℕ) :
    lowerSuzukiUnnormalizedLayer S D z k =
      sourceDiscreteEuler S z * lowerSuzukiNormalizedLayer S D 0 z k := by
  classical
  rw [lowerSuzukiNormalizedLayer_eq_primeSum]
  simp only [Nat.zero_le, Finset.filter_true]
  rw [Finset.mul_sum]
  unfold lowerSuzukiUnnormalizedLayer
  apply Finset.sum_congr rfl
  intro q hq
  rw [← sourceDiscreteEuler_mul_suzukiSuffixRatio S hq]
  ring

/-- Hence the canonical accumulator is the full Euler product times the finite
sum of normalized lower Suzuki layers. -/
theorem lowerRosserBoundaryAccum_supportedBelow_eq_euler_mul_sum_normalizedLayers
    (S : BoundingSieve) (D z : ℕ) :
    lowerRosserBoundaryAccum S.nu D ∅ (suzukiSupportedBelowList S z) =
      sourceDiscreteEuler S z *
        ∑ k ∈ Finset.range ((suzukiSupportedBelow S z).card + 1),
          lowerSuzukiNormalizedLayer S D 0 z k := by
  rw [lowerRosserBoundaryAccum_supportedBelow_eq_sum_unnormalizedLayers]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lowerSuzukiUnnormalizedLayer_eq_euler_mul_normalizedLayer]

/-- At every legal source level, each actual even Suzuki source layer is the
Euler product times its normalized lower-boundary layer. -/
theorem suzukiSourceV_even_eq_euler_mul_normalizedLayer
    (S : BoundingSieve) (D z k : ℕ) (hzD : z ≤ D) :
    suzukiSourceV S (2 * (k + 1)) D z =
      sourceDiscreteEuler S z * lowerSuzukiNormalizedLayer S D 0 z k := by
  rw [suzukiSourceV_even_eq_lowerRosserEvenBoundaryLayerMass,
    lowerRosserEvenBoundaryLayerMass_eq_unnormalizedLayer S D z k hzD,
    lowerSuzukiUnnormalizedLayer_eq_euler_mul_normalizedLayer]

/-- Exact finite normalization identity for Suzuki's actual even parity sum. -/
theorem suzukiActualT_even_eq_euler_mul_sum_normalizedLayers
    (S : BoundingSieve) (D z m : ℕ) (hzD : z ≤ D) :
    suzukiActualT S (2 * m) D z =
      sourceDiscreteEuler S z *
        ∑ k ∈ Finset.range m, lowerSuzukiNormalizedLayer S D 0 z k := by
  rw [suzukiActualT_even_eq_sum_lowerRosserEvenBoundaryLayerMass,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lowerRosserEvenBoundaryLayerMass_eq_unnormalizedLayer S D z k hzD,
    lowerSuzukiUnnormalizedLayer_eq_euler_mul_normalizedLayer]

/-- Once all finite supported depths are included, the actual Suzuki parity sum
is literally the canonical lower-Rosser accumulator. -/
theorem suzukiActualT_all_supported_depths_eq_lowerRosserBoundaryAccum
    (S : BoundingSieve) (D z : ℕ) (hzD : z ≤ D) :
    suzukiActualT S (2 * ((suzukiSupportedBelow S z).card + 1)) D z =
      lowerRosserBoundaryAccum S.nu D ∅ (suzukiSupportedBelowList S z) := by
  rw [suzukiActualT_even_eq_sum_lowerRosserEvenBoundaryLayerMass]
  apply Eq.symm
  rw [lowerRosserBoundaryAccum_supportedBelow_eq_sum_unnormalizedLayers]
  apply Finset.sum_congr rfl
  intro k hk
  exact (lowerRosserEvenBoundaryLayerMass_eq_unnormalizedLayer S D z k hzD).symm


end MathlibNt.SieveTheory
