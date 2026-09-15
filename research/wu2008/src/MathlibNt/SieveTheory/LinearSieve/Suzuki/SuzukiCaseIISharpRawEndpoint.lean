import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointTransport

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Sharp source-native Case-II assembly at `β = 2`.

Unlike `caseII_total_le_concrete_finiteSourceLayer_add_errorEnvelope`, this
uses the unnormalised source assembly and therefore retains the base-layer loss
at its native `1 / (s * log D)` scale. -/
theorem caseII_total_le_concrete_finiteSourceLayer_add_rawBase
    (S : BoundingSieve)
    {K s endpointErr : ℝ} {N D y z : ℕ}
    (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
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
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hbase : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * 3 ^ 2 / (s * Real.log (D : ℝ))) :=
    suzukiSourceV_one_le_V_mul_fOne_add_localError
      hDone hs hs3 hz hz2 hK hlocal
  have hendpoint' :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        suzukiVProduct S (z : ℝ) *
          (((2 : ℝ) + 1) / s * finiteSourceLayer 1 2 N ((2 : ℝ) + 1)) +
            endpointErr := by
    convert hendpoint using 1; norm_num
  have hbase' : suzukiSourceV S 1 D z ≤
      suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 1 s +
          K * ((2 : ℝ) + 1) ^ 2 / (s * Real.log (D : ℝ))) := by
    convert hbase using 1; norm_num
  have hraw := caseII_source_finite_assembly
    (S := S) (β := (2 : ℝ)) (s := s) (K := K)
    (Vz := suzukiVProduct S (z : ℝ)) (endpointErr := endpointErr)
    hN hs (by norm_num at hs3 ⊢; exact hs3)
    hyz hyLower hyUpper hendpoint' hbase'
  convert hraw using 1; norm_num

/-- Full production endpoint transport followed by the sharp source-native
Case-II assembly.  Every term of `caseIIEndpointErr` is retained (including the
Euler-product ratio excess), while the source `V₁` base loss remains
`9 K / (s log D)` rather than being normalised to a bare `9 K` multiple of the
error envelope.  No legacy extended-layer object occurs. -/
theorem caseII_total_le_from_caseI_endpoint_explicit_rawBase
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {σ C C1 K ΘK Δ d B0 s : ℝ}
    (hH : Section13HatContract H 2)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hpower : (D : ℝ) ^ (1 / 3 : ℝ) = (y : ℝ))
    (hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
    (h3σ : 3 ≤ σ)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hDlarge : 2 * Real.log 2 ≤ Real.log (D : ℝ))
    (hwy : (D : ℝ) ^ (1 / σ) ≤ (y : ℝ))
    (hy2 : 2 ≤ (y : ℝ))
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
    (hΔ0 : 0 ≤ Δ) (_hΔ1 : Δ ≤ 1) (_hd : 0 ≤ d)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (y : ℝ) →
      2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (y : ℝ) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) → (p : ℝ) < (y : ℝ) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)))
    (hs : 0 < s) (hs3 : s ≤ 3)
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hz : (z : ℝ) = (D : ℝ) ^ (1 / s)) (hz2 : 2 ≤ (z : ℝ)) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
        caseIIEndpointErr S H N D y z d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) := by
  have hDone : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hF : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    caseII_finiteSourceLayer_three_nonneg hN
  have hSigma11 : 0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ :=
    caseIIEndpointSigma11_nonneg hN hw2
  have hQD : 0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K :=
    caseIIEndpointQD_nonneg hH hDone h3σ hw2 hC
  have hcaseIRaw := caseII_endpoint_le_concrete_finiteSourceLayer_add_qD
    (S := S) (H := H) (N := N) (D := D) (y := y)
    (β := (2 : ℝ)) (σ := σ) (C := C) (C1 := C1) (K := K)
    (ΘK := ΘK) (Δ := Δ) (d := d) (B0 := B0)
    hH hN hN2 hycube (by convert hpower using 1; norm_num) hyDhalf
    (by norm_num at h3σ ⊢; exact h3σ) hDone
    (by norm_num at hDlarge ⊢; exact hDlarge) hwy hy2 hw2 hEndpoint
    (by norm_num at hnu ⊢; exact hnu) hC
    (by norm_num at hlog ⊢; exact hlog)
    (by norm_num at hSourceDomain ⊢; exact hSourceDomain)
    (by norm_num at hClaim14_6_i ⊢; exact hClaim14_6_i)
    (by norm_num at hErrorDomain ⊢; exact hErrorDomain)
    (by norm_num at hIH ⊢; exact hIH)
    (by norm_num at hErrorThreshold ⊢; exact hErrorThreshold) hK hlocal
    hClaim14_6_ii hΔ0 hCeilFull hT hClaim14_13
  have hcaseI :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        B0 + suzukiVProduct S (y : ℝ) *
          (finiteSourceLayer 1 2 N 3 + caseIIEndpointSigma11 K N (D : ℝ) σ) +
          suzukiVProduct S (y : ℝ) *
            caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
    convert hcaseIRaw using 1;
      simp only [caseIIEndpointSigma11, caseIIEndpointQD]; ring
  have hVratio := suzukiVProduct_le_dimensionOne_ratio S hy2 hyz hlocal
  have hlogRatio : Real.log (z : ℝ) / Real.log (y : ℝ) = 3 / s :=
    caseII_log_ratio_of_power_identities hD hs hpower.symm hz
  have hendpoint := caseII_endpoint_transport_explicit S H hs hlogRatio hVratio
    hF hSigma11 hQD hcaseI
  exact caseII_total_le_concrete_finiteSourceLayer_add_rawBase
    S hN hD hs hs3 (by linarith) hyz hyLower hyUpper hz hz2 hlocal hendpoint


end MathlibNt.SieveTheory
