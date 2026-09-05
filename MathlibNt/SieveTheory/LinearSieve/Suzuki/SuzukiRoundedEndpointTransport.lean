import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedCaseIEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpRawEndpoint
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
      rfl hzr2 hK hlocal using 1 <;> ring
  have hbase : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s + 9 * K / (s * Real.log (D : ℝ))) := by
    rw [hVz]
    convert hbase0 using 1 <;> ring
  have hendpoint' :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          (((2 : ℝ) + 1) / s * finiteSourceLayer 1 2 N ((2 : ℝ) + 1)) +
          endpointErr := by
    rw [hVz]
    convert hendpoint using 1 <;> norm_num
  have hbase' : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * ((2 : ℝ) + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
    convert hbase using 1 <;> ring
  have hraw := caseII_source_finite_assembly
    (S := S) (β := (2 : ℝ)) (s := s) (K := K)
    (Vz := suzukiVProduct S (z : ℝ)) (endpointErr := endpointErr)
    hN hs (by norm_num at hs3 ⊢; exact hs3)
    hyz hyLower hyUpper hendpoint' hbase'
  convert hraw using 1 <;> ring

/-- Double-rounded sharp Case-II endpoint transport.

The natural cutoffs are `y = ceil(D^(1/3))` and `z = ceil(D^(1/s))`.
Dimension-one transport and the logarithmic ratio are carried out only at the
exact real roots.  The two Euler products are then returned exactly to their
natural-ceiling cutoffs; no equality between a cast natural cutoff and a real
root is assumed. -/
theorem caseII_total_le_from_caseI_endpoint_explicit_rawBase_natCeil
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {σ C C1 K ΘK Δ d B0 s : ℝ}
    (hH : Section13HatContract H 2)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hyceil : y = ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
    (hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
    (h3σ : 3 ≤ σ)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ))
    (hwy : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / (3 : ℝ)))
    (hy2 : 2 ≤ (y : ℝ))
    (hyr2 : 2 ≤ (D : ℝ) ^ (1 / (3 : ℝ)))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hEndpoint : Claim14_5Regime 2 (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ S.nu p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1))
    (hClaim14_6_i : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      inheritedCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ 3)
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon < 3)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ0 : 0 ≤ Δ)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)))
    (hs : 0 < s) (hs3 : s ≤ 3)
    (hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s))
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hzr2 : 2 ≤ (D : ℝ) ^ (1 / s)) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
        caseIIRoundedTransportErr S H N (D : ℝ)
          ((D : ℝ) ^ (1 / (3 : ℝ))) ((D : ℝ) ^ (1 / s))
          d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) * (9 * K / (s * Real.log (D : ℝ))) := by
  let yr : ℝ := (D : ℝ) ^ (1 / (3 : ℝ))
  let zr : ℝ := (D : ℝ) ^ (1 / s)
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hF : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    caseII_finiteSourceLayer_three_nonneg hN
  have hSigma11 : 0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ :=
    caseIIEndpointSigma11_nonneg hN hw2
  have hQD : 0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K :=
    caseIIEndpointQD_nonneg hH hDone h3σ hw2 hC
  have hcaseIRaw :=
    caseII_endpoint_le_concrete_finiteSourceLayer_add_qD_natCeil
      (S := S) (H := H) (N := N) (D := D) (y := y)
      (β := (2 : ℝ)) (σ := σ) (C := C) (C1 := C1) (K := K)
      (ΘK := ΘK) (Δ := Δ) (d := d) (B0 := B0)
      hH hN hN2 hycube (by convert hyceil using 1 <;> norm_num) hyDhalf
      (by norm_num at h3σ ⊢; exact h3σ) hDone
      (by norm_num at hDlarge ⊢; exact hDlarge)
      (by convert hwy using 1 <;> norm_num) hy2
      (by convert hyr2 using 1 <;> norm_num) hw2 hEndpoint
      (by norm_num at hnu ⊢; exact hnu) hC
      (by norm_num at hlog ⊢; exact hlog)
      (by norm_num at hSourceDomain ⊢; exact hSourceDomain)
      (by norm_num at hClaim14_6_i ⊢; exact hClaim14_6_i)
      (by norm_num at hErrorDomain ⊢; exact hErrorDomain)
      (by norm_num at hIH ⊢; exact hIH)
      (by norm_num at hErrorThreshold ⊢; exact hErrorThreshold) hK hlocal
      hClaim14_6_ii hΔ0
      (by convert hCeilFull using 1 <;> norm_num)
      (by convert hT using 1 <;> norm_num)
      (by convert hClaim14_13 using 1 <;> norm_num)
  have hVy : suzukiVProduct S (y : ℝ) = suzukiVProduct S yr := by
    exact suzukiVProduct_natCeil_eq S (by simpa [yr] using hyceil)
  have hVz : suzukiVProduct S (z : ℝ) = suzukiVProduct S zr := by
    exact suzukiVProduct_natCeil_eq S (by simpa [zr] using hzceil)
  have hcaseI :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        B0 + suzukiVProduct S yr *
          (finiteSourceLayer 1 2 N 3 + caseIIEndpointSigma11 K N (D : ℝ) σ) +
          suzukiVProduct S yr * caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
    rw [← hVy]
    convert hcaseIRaw using 1 <;>
      simp only [caseIIEndpointSigma11, caseIIEndpointQD] <;> ring
  have hVratio : suzukiVProduct S yr ≤
      suzukiVProduct S zr * (Real.log zr / Real.log yr) *
        (1 + K / Real.log yr) := by
    have hratio := hlocal yr zr (by simpa [yr] using hyr2)
      (by simpa [yr, zr] using hyrzr)
    have hprod : suzukiVProduct S yr =
        suzukiVProduct S zr * suzukiLocalRatio S yr zr := by
      classical
      let A := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < yr)
      let B := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => yr ≤ (p : ℝ) ∧ (p : ℝ) < zr)
      let Cset := S.prodPrimes.primeFactors.filter
        (fun p : ℕ => (p : ℝ) < zr)
      have hdisj : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro p hpA hpB
        simp only [A, B, mem_filter] at hpA hpB
        linarith [hpA.2, hpB.2.1]
      have hunion : A ∪ B = Cset := by
        ext p
        simp only [A, B, Cset, Finset.mem_union, mem_filter]
        constructor
        · rintro (hpA | hpB)
          · exact ⟨hpA.1, hpA.2.trans_le (by simpa [yr, zr] using hyrzr)⟩
          · exact ⟨hpB.1, hpB.2.2⟩
        · intro hpC
          by_cases hp : (p : ℝ) < yr
          · exact Or.inl ⟨hpC.1, hp⟩
          · exact Or.inr ⟨hpC.1, le_of_not_gt hp, hpC.2⟩
      have hBne : (∏ p ∈ B, (1 - S.nu p)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        have hpP : p ∈ S.prodPrimes.primeFactors :=
          (mem_filter.mp hp).1
        exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p
          (Nat.prime_of_mem_primeFactors hpP)
          (Nat.mem_primeFactors.mp hpP).2.1))
      unfold suzukiVProduct suzukiLocalRatio
      change (∏ p ∈ A, (1 - S.nu p)) =
        (∏ p ∈ Cset, (1 - S.nu p)) *
          ∏ p ∈ B, (1 - S.nu p)⁻¹
      rw [← hunion, Finset.prod_union hdisj]
      rw [Finset.prod_inv_distrib]
      field_simp [hBne]
    rw [hprod]
    simpa [suzukiLocalRatio, mul_assoc] using
      (mul_le_mul_of_nonneg_left hratio (suzukiVProduct_pos S zr).le)
  have hlogRatio : Real.log zr / Real.log yr = 3 / s := by
    exact caseII_log_ratio_of_power_identities
      (D := (D : ℝ)) (y := yr) (z := zr) hD hs (by simp [yr]) (by simp [zr])
  rw [hlogRatio] at hVratio
  have hmain := mul_le_mul_of_nonneg_right hVratio hF
  have h11 := mul_le_mul_of_nonneg_right hVratio hSigma11
  have hq := mul_le_mul_of_nonneg_right hVratio hQD
  have hendpoint :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S zr * ((3 / s) * finiteSourceLayer 1 2 N 3) +
          caseIIRoundedTransportErr S H N (D : ℝ) yr zr
            d Δ σ C K B0 s := by
    unfold caseIIRoundedTransportErr
    calc
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
          B0 + suzukiVProduct S yr * finiteSourceLayer 1 2 N 3 +
            suzukiVProduct S yr * caseIIEndpointSigma11 K N (D : ℝ) σ +
            suzukiVProduct S yr *
              caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
        nlinarith [hcaseI]
      _ ≤ B0 +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) * finiteSourceLayer 1 2 N 3 +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) * caseIIEndpointSigma11 K N (D : ℝ) σ +
          (suzukiVProduct S zr * (3 / s) *
            (1 + K / Real.log yr)) *
              caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
        gcongr
      _ = suzukiVProduct S zr * ((3 / s) * finiteSourceLayer 1 2 N 3) +
          (B0 + suzukiVProduct S zr *
            ((3 / s) * (K / Real.log yr) * finiteSourceLayer 1 2 N 3 +
              (3 / s) * (1 + K / Real.log yr) *
                caseIIEndpointSigma11 K N (D : ℝ) σ +
              (3 / s) * (1 + K / Real.log yr) *
                caseIIEndpointQD H N (D : ℝ) d Δ σ C K)) := by ring
  have hfinal := caseII_total_le_concrete_finiteSourceLayer_add_rawBase_natCeil
    S hN hD hs hs3 (by linarith) hyz hyLower hyUpper hzceil hzr2 hlocal hendpoint
  simpa [yr, zr] using hfinal


end MathlibNt.SieveTheory
