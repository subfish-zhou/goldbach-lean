import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedTransportRefactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedTransportErrorBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiRoundedTransportExactRatio
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIISourceLargeLogUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- Direct double-rounded Case-II assembly into the exact-ratio source-large
relative bracket.  This is the K-uniform consumer of the rounded transport
packet; no abstract endpoint-error premise is exposed. -/
theorem caseII_total_le_doubleRounded_direct_sourceLarge_relative_natCeil_of_errorTransport
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
    (hErrorTransport : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ 3,
      errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (recursiveCoordinate D p) ≤
        errorEnvelope H (N - 1) ((D ⌈/⌉ p : ℕ) : ℝ) d
          (inheritedCoordinate D p))
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ 3)
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ 3)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
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
    (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hyrzr : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (D : ℝ) ^ (1 / s))
    (hyz : y ≤ z) (hyLower : (y - 1) ^ 3 < D) (hyUpper : D ≤ y ^ 3)
    (hzceil : z = ⌈(D : ℝ) ^ (1 / s)⌉₊)
    (hzr2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hsmall : (3 : ℝ) ^ d ≤ Real.log (D : ℝ))
    (hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s)
    (hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ))
    (hClaim14_6_iii : (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
      (1 - 1 / σ) ^ (1 - Δ) *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3)
    (hLambdaCubic : lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 3 ≤
      perturbation (D : ℝ) d 0 3 *
        lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s)
    (hP : 3 ≤ C * Real.exp (Real.sqrt K))
    (hPE : 1 ≤ (C * Real.exp (Real.sqrt K)) *
      errorEnvelope H N (D : ℝ) d s) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      B0 + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K)) *
            errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIConcreteRoundedRelativeBracketSourceLarge
              N (D : ℝ) d Δ σ K) := by

  let yr : ℝ := (D : ℝ) ^ (1 / (3 : ℝ))
  let zr : ℝ := (D : ℝ) ^ (1 / s)
  have hs : 0 < s := zero_lt_one.trans hs1
  have hK0 : 0 ≤ K := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hF0 : 0 ≤ finiteSourceLayer 1 2 N 3 := caseII_finiteSourceLayer_three_nonneg hN
  have hNm : (N - 1) % 2 = 0 := by
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hF1 : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hSharp :=
    caseII_total_le_from_caseI_endpoint_explicit_rawBase_natCeil_of_errorTransport
      (S := S) (H := H) (N := N) (D := D) (y := y) (z := z)
      (σ := σ) (C := C) (C1 := C1) (K := K) (ΘK := ΘK)
      (Δ := Δ) (d := d) (B0 := B0) (s := s)
      hH hN hN2 hycube hyceil hyDhalf h3σ hD hDlarge hwy hy2 hyr2 hw2
      hEndpoint hnu hC hlog hSourceDomain hErrorTransport hIH
      hErrorThreshold hK hlocal hClaim14_6_ii hΔ0.le hCeilFull hT
      hClaim14_13 hs hs3 hyrzr hyz hyLower hyUpper hzceil hzr2
  have hPacket :=
    caseII_rounded_transportErr_le_positiveDelta_relative_packet_sourceLarge_coefficients
      (S := S) (H := H) (N := N) (D := D) (z := z)
      (yr := yr) (zr := zr) (d := d) (Δ := Δ) (σ := σ)
      (C := C) (K := K) (B0 := B0) (s := s)
      hH hN hD hΔ0 hΔ1 h3σ hs1 hK0 hC hsmall hE hP rfl rfl
      (by simpa [zr] using hzceil)
  have hIntegral := caseIIRoundedIntegralPart_source_relative
    (H := H) (N := N) (D := (D : ℝ)) (yr := yr)
    (d := d) (Δ := Δ) (σ := σ) (C := C) (K := K) (s := s)
    rfl ((Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD) hs hC hK0
    hcut hClaim14_6_iii hLambdaCubic
  let P : ℝ := C * Real.exp (Real.sqrt K)
  let E : ℝ := errorEnvelope H N (D : ℝ) d s
  let L : ℝ := (Real.log (D : ℝ)) ^ (-Δ)
  let R : ℝ := (1 + 3 * K / Real.log (D : ℝ)) *
    (1 - 1 / σ) ^ (1 - Δ) * perturbation (D : ℝ) d 0 3
  let C_end := caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K
  have hEndpointScaled :
      caseIIRoundedTransportErr S H N (D : ℝ) yr zr d Δ σ C K B0 s +
          suzukiVProduct S (z : ℝ) *
            (K * 3 ^ 2 / (s * Real.log (D : ℝ))) ≤
        B0 + suzukiVProduct S (z : ℝ) *
          (P * E * L * R + P * E * L * C_end) := by
    calc
      _ ≤ B0 + suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart H N (D : ℝ) yr d Δ σ C K s +
            P * E * L * C_end) := by
              simpa [P, E, L, C_end, yr, zr] using hPacket
      _ ≤ B0 + suzukiVProduct S (z : ℝ) *
          (P * E * L * R + P * E * L * C_end) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (suzukiVProduct_pos S (z : ℝ)).le
        exact add_le_add (by simpa [P, E, L, R] using hIntegral) le_rfl
  calc
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
        suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
          (caseIIRoundedTransportErr S H N (D : ℝ) yr zr
            d Δ σ C K B0 s + suzukiVProduct S (z : ℝ) *
              (K * 3 ^ 2 / (s * Real.log (D : ℝ)))) := by
        convert hSharp using 1 <;> ring
    _ ≤ suzukiVProduct S (z : ℝ) * finiteSourceLayer 1 2 N s +
          (B0 + suzukiVProduct S (z : ℝ) *
            (P * E * L * R + P * E * L * C_end)) := by
        linarith [hEndpointScaled]
    _ = B0 + suzukiVProduct S (z : ℝ) *
        (finiteSourceLayer 1 2 N s +
          (C * Real.exp (Real.sqrt K)) *
            errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ) *
            caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ) d Δ σ K) := by
      dsimp [P, E, L, R, C_end, caseIIConcreteRoundedRelativeBracketSourceLarge]
      ring



end MathlibNt.SieveTheory
