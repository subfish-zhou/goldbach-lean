import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedEndpointError

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The complete endpoint remainder after transporting the cubic endpoint from
`yr = D^(1/3)` to `zr = D^(1/s)`.  In contrast with the legacy natural-cutoff
wrapper, both analytic cutoff coordinates are the exact real roots. -/
noncomputable def caseIIRoundedTransportErr
    (S : BoundingSieve) (H : Section13HatLayers) (N : ℕ)
    (D yr zr d Δ σ C K B0 s : ℝ) : ℝ :=
  B0 + suzukiVProduct S zr *
    ((3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
      (3 / s) * (1 + K / Real.log yr) *
        caseIIEndpointSigma11 K N D σ +
      (3 / s) * (1 + K / Real.log yr) *
        caseIIEndpointQD H N D d Δ σ C K)

/-- Sharp source-native Case-II assembly when the target cutoff is the natural
ceiling of the exact real power coordinate. -/
theorem caseII_total_le_concrete_finiteSourceLayer_add_rawBase_natCeil
    (S : BoundingSieve)
    {K s endpointErr : ℝ} {N D y z : ℕ}
    (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hs : 0 < s) (hs3 : s ≤ 3) (hK : 0 ≤ K)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hzr2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
          ((3 / s) * finiteSourceLayer 1 2 N 3) + endpointErr) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s + endpointErr +
        suzukiVProduct S (z : ℝ) * (9 * K / (s * Real.log (D : ℝ))) := by
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hVz : suzukiVProduct S (z : ℝ) =
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) :=
    suzukiVProduct_natCeil_eq S hzceil
  have hDnat : 0 < D := by omega
  have hzr0 : 0 < (D : ℝ) ^ (1 / s) :=
    natCast_rpow_one_div_pos hDnat s
  have hVOneRound :
      suzukiVOne S (D : ℝ) 2 (z : ℝ) =
        suzukiVOne S (D : ℝ) 2 ((D : ℝ) ^ (1 / s)) := by
    have hNorm :
        suzukiVOneNormalized S (D : ℝ) 2 (z : ℝ) =
          suzukiVOneNormalized S (D : ℝ) 2 ((D : ℝ) ^ (1 / s)) := by
      unfold suzukiVOneNormalized suzukiLemmaEightSixPrimeSum
      apply Finset.sum_congr
      · ext p
        simp only [mem_filter]
        rw [Nat.cast_lt, nat_lt_natCeil_iff_lt_real hzr0 hzceil]
      · intro p hp
        have hsuffix :
            (∏ q ∈ S.prodPrimes.primeFactors.filter
                (fun q : ℕ => p ≤ q ∧ (q : ℝ) < (z : ℝ)),
              (1 - S.nu q)⁻¹) =
              ∏ q ∈ S.prodPrimes.primeFactors.filter
                (fun q : ℕ => p ≤ q ∧
                  (q : ℝ) < (D : ℝ) ^ (1 / s)),
                (1 - S.nu q)⁻¹ := by
          congr 1
          ext q
          simp only [mem_filter]
          rw [Nat.cast_lt, nat_lt_natCeil_iff_lt_real hzr0 hzceil]
        rw [hsuffix]
    unfold suzukiVOne
    rw [suzukiVProduct_natCeil_eq S hzceil, hNorm]
  have hbase0 : suzukiSourceV S 1 D z ≤
      suzukiVProduct S ((D : ℝ) ^ (1 / s)) *
        (finiteSourceLayer 1 2 1 s +
          K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
    rw [suzukiSourceV_one_eq_suzukiVOne_two, hVOneRound]
    convert suzukiVOne_le_V_mul_fOne_add_localError
      (S := S) (D := (D : ℝ)) (β := (2 : ℝ))
      (z := (D : ℝ) ^ (1 / s)) (s := s) (K := K)
      hDone (by norm_num) hs (by norm_num at hs3 ⊢; exact hs3)
      rfl hzr2 hK hlocal using 1; ring
  have hbase : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) := by
    rw [hVz]
    convert hbase0 using 1; ring
  have hendpoint' :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          (((2 : ℝ) + 1) / s * finiteSourceLayer 1 2 N ((2 : ℝ) + 1)) +
          endpointErr := by
    rw [hVz]
    convert hendpoint using 1; norm_num
  have hbase' : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * ((2 : ℝ) + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
    convert hbase using 1; ring
  have hraw := caseII_source_finite_assembly
    (S := S) (β := (2 : ℝ)) (s := s) (K := K)
    (Vz := suzukiVProduct S (z : ℝ)) (endpointErr := endpointErr)
    hN hs (by norm_num at hs3 ⊢; exact hs3)
    hyz hyLower hyUpper hendpoint' hbase'
  convert hraw using 1; ring


end MathlibNt.SieveTheory
