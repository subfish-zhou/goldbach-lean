import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceCaseIICutoff
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseII
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiVOneNaturalBridge

open scoped Classical BigOperators Interval
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The source-faithful base layer is exactly Suzuki's finite `V₁` object at
`β = 2`.  This identification uses the literal source carrier `D ≤ p³` and no
legacy extended-layer object. -/
theorem suzukiSourceV_one_eq_suzukiVOne_two
    (S : BoundingSieve) (D z : ℕ) :
    suzukiSourceV S 1 D z = suzukiVOne S (D : ℝ) 2 (z : ℝ) := by
  classical
  rw [suzukiSourceV_one, suzukiVOne, suzukiVOneNormalized, suzukiYOne_two,
    suzukiLemmaEightSixPrimeSum, Finset.mul_sum]
  apply Finset.sum_congr
  · ext p
    simp only [suzukiSupportedBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hpP, hpz⟩, hp3⟩
      exact ⟨hpP, (cube_carrier_bridge D p).mp hp3, by exact_mod_cast hpz⟩
    · rintro ⟨hpP, hrootp, hpz⟩
      exact ⟨⟨hpP, by exact_mod_cast hpz⟩,
        (cube_carrier_bridge D p).mpr hrootp⟩
  · intro p hp
    have hpz : (p : ℝ) < (z : ℝ) := (Finset.mem_filter.mp hp).2.2
    simp only [mul_one]
    symm
    have hratio :
        (∏ q ∈ S.prodPrimes.primeFactors.filter
            (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)),
          (1 - S.nu q)⁻¹) = suzukiLocalRatio S (p : ℝ) (z : ℝ) := by
      unfold suzukiLocalRatio
      congr 2
      ext q
      simp
    rw [hratio]
    calc
      suzukiVProduct S (z : ℝ) *
          (S.nu p * suzukiLocalRatio S (p : ℝ) (z : ℝ)) =
          S.nu p * (suzukiVProduct S (z : ℝ) *
            suzukiLocalRatio S (p : ℝ) (z : ℝ)) := by ring
      _ = S.nu p * sourceDiscreteEuler S p := by
        rw [suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S hpz]


/-- Pure source-native finite Case-II assembly.  The exact ceiling-cube
hypotheses produce Suzuki's cutoff identity internally; the two analytic inputs
are already stated on the source parity sum and source `V₁`. -/
theorem caseII_source_finite_assembly
    {S : BoundingSieve} {β s K Vz endpointErr : ℝ} {N D y z : ℕ}
    (hN : Odd N) (hs : 0 < s) (hsβ : s ≤ β + 1)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr)
    (hbase : suzukiSourceV S 1 D z ≤
      Vz * (finiteSourceLayer 1 β 1 s +
        K * (β + 1) ^ 2 / (s * Real.log (D : ℝ)))) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      Vz * finiteSourceLayer 1 β N s + endpointErr +
        Vz * (K * (β + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
  rw [suzukiSourceParitySum_caseII_cut_of_ceilingCube S hN hyz hyLower hyUpper]
  calc
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) +
        suzukiSourceV S 1 D z ≤
      Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr +
        Vz * (finiteSourceLayer 1 β 1 s +
          K * (β + 1) ^ 2 / (s * Real.log (D : ℝ))) :=
      add_le_add hendpoint hbase
    _ = Vz * finiteSourceLayer 1 β N s + endpointErr +
          Vz * (K * (β + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
      rw [← finiteSourceLayer_caseII_identity hN hs hsβ]
      ring


end MathlibNt.SieveTheory
