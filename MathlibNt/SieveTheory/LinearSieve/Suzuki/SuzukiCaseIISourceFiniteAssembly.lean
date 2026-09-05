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

/-- Source-native `V₁` base bound.  Unlike the older natural bridge, both sides
refer directly to `suzukiSourceV`; no extended Section-14 object occurs. -/
theorem suzukiSourceV_one_le_V_mul_fOne_add_localError
    {S : BoundingSieve} {D z : ℕ} {s K : ℝ}
    (hD : 1 < (D : ℝ)) (hs : 0 < s) (hs3 : s ≤ 3)
    (hz : (z : ℝ) = (D : ℝ) ^ (1 / s)) (hz2 : 2 ≤ (z : ℝ))
    (hK : 0 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiSourceV S 1 D z ≤ suzukiVProduct S (z : ℝ) *
      (finiteSourceLayer 1 2 1 s + K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
  rw [suzukiSourceV_one_eq_suzukiVOne_two]
  convert suzukiVOne_le_V_mul_fOne_add_localError
    (S := S) (D := (D : ℝ)) (β := (2 : ℝ)) (z := (z : ℝ))
    (s := s) (K := K) hD (by norm_num) hs (by norm_num at hs3 ⊢; exact hs3)
    hz hz2 hK hlocal using 1
  all_goals norm_num

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

/-- Source-native Case-II assembly with the base loss normalized to the same
literal error envelope as the endpoint induction error. -/
theorem caseII_source_finite_assembly_normalized
    {S : BoundingSieve} {H : Section13HatLayers}
    {β d Δ K s Vz endpointErr : ℝ} {N D y z : ℕ}
    (hH : Section13HatContract H β) (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ)) (hd : 0 ≤ d)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hs : 0 < s) (hsβ : s ≤ β + 1) (hK : 0 ≤ K) (hVz : 0 ≤ Vz)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr)
    (hbase : suzukiSourceV S 1 D z ≤
      Vz * (finiteSourceLayer 1 β 1 s +
        K * (β + 1) ^ 2 / (s * Real.log (D : ℝ)))) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      Vz * finiteSourceLayer 1 β N s + endpointErr +
        Vz * ((K * (β + 1) ^ 2 / (β - 1)) *
          errorEnvelope H N (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  have hassembly := caseII_source_finite_assembly
    (S := S) (β := β) (s := s) (K := K) (Vz := Vz)
    (endpointErr := endpointErr) hN hs hsβ hyz hyLower hyUpper hendpoint hbase
  have hnorm := mul_le_mul_of_nonneg_left
    (caseII_base_error_le_errorEnvelope hH hN hD hd hΔ0 hΔ1 hs hsβ hK) hVz
  nlinarith [hassembly, hnorm]

/-- Fully concrete source-native Case-II assembly at Suzuki's source parameter
`β = 2`.  It consumes the source endpoint at the exact natural cube cutoff and
proves the source `V₁` estimate internally from the local-product bound. -/
theorem caseII_total_le_concrete_finiteSourceLayer_add_errorEnvelope
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ K s endpointErr : ℝ} {N D y z : ℕ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ)) (hd : 0 ≤ d)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hs : 0 < s) (hs3 : s ≤ 3) (hK : 0 ≤ K)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hz : (z : ℝ) = (D : ℝ) ^ (1 / s)) (hz2 : 2 ≤ (z : ℝ))
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          ((3 / s) * finiteSourceLayer 1 2 N 3) + endpointErr) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s + endpointErr +
        suzukiVProduct S (z : ℝ) *
          ((K * 3 ^ 2 / (2 - 1)) *
            errorEnvelope H N (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
  have hbase : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s + K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
    apply suzukiSourceV_one_le_V_mul_fOne_add_localError
    · exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
    · exact hs
    · exact hs3
    · exact hz
    · exact hz2
    · exact hK
    · exact hlocal
  have hendpoint' :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          (((2 : ℝ) + 1) / s * finiteSourceLayer 1 2 N ((2 : ℝ) + 1)) +
            endpointErr := by
    convert hendpoint using 1
    all_goals norm_num
  have hbase' : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * ((2 : ℝ) + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
    convert hbase using 1
    all_goals norm_num
  have hfinal := caseII_source_finite_assembly_normalized
    (S := S) (H := H) (β := (2 : ℝ)) (d := d) (Δ := Δ) (K := K)
    (s := s) (Vz := suzukiVProduct S (z : ℝ)) (endpointErr := endpointErr)
    hH hN hD hd hΔ0 hΔ1 hs (by norm_num at hs3 ⊢; exact hs3) hK
    (suzukiVProduct_pos S (z : ℝ)).le hyz hyLower hyUpper
    hendpoint' hbase'
  convert hfinal using 1
  all_goals norm_num


end MathlibNt.SieveTheory
