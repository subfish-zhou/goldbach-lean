import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseITotalInequality
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIMiddleConcreteProvider
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveCarrierEquality

open scoped Classical BigOperators
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Final concrete finite Case-I assembly.  The total source inequality is
specialized to Suzuki's Euler product, while the exact carrier equality moves
the full-support `sigmaTwelve` estimate onto the supported carrier required by
the recurrence assembly. -/
theorem caseI_total_le_concrete_finiteSourceLayer_add_qD
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {β σ s C C1 K ΘK Δ d B0 : ℝ}
    (hH : Section13HatContract H β)
    (hN2 : 2 ≤ N)
    (hbase : Odd N → suzukiSourceV S 1 D z = 0)
    (hcube : ∀ n ∈ sourceParityIndices N, 2 ≤ n → Odd n →
      ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D)
    (hdom : CaseIThreeRangeDomain D z σ s)
    (hcaseITau : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ))
    (hcaseI : Claim14_5CaseI β N s σ)
    (hEndpoint : Claim14_5Regime β (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      0 ≤ S.nu p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1))
    (hClaim14_6_i : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S z)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ s)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hsm1dom : s - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hD : 1 < (D : ℝ))
    (hz2 : 2 ≤ (z : ℝ))
    (hv2 : 2 ≤ (D : ℝ) ^ (1 / s))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwv : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / s))
    (hvz : (D : ℝ) ^ (1 / s) ≤ (z : ℝ))
    (hErrorThreshold : H.betaHat + (ErrorSign.ofDepth N).epsilon < s)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ : 0 ≤ Δ)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / s) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
      B0 +
        (suzukiVProduct S z *
            (finiteSourceLayer 1 β N s +
              (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (s - 1) /
                Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)) +
          C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
            (Real.log (D : ℝ)) ^ (-Δ) *
            ((1 / s) * (∫ t in s..σ,
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
              (6 * K ^ 2 *
                  qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s /
                Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))) := by
  have hConcrete :=
    sigmaEleven_add_sigmaTwelve_suzukiVProduct_le_finiteSourceLayer_add_qD
      (S := S) (H := H) (β := β) (C := C) (K := K) (d := d) (Δ := Δ)
      (s := s) (τ := s) (σ := σ) (N := N) (D := D) (znat := z)
      hH hsdom hsm1dom le_rfl hcaseI.2 hD hz2 hv2 hw2 hwv hvz hz.symm
      hErrorThreshold hK hlocal hClaim14_6_ii hC hΔ hCeilFull hT hClaim14_13
  have hCarrier := sigmaTwelve_supportedBelow_eq_full S
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) C K Δ N D z σ s hvz
  apply caseI_total_le_sigma0_add_sigma11_add_sigma12
    (S := S) (V := fun p => suzukiVProduct S p) (H := H)
    (N := N) (D := D) (z := z) (β := β) (σ := σ) (s := s)
    (C := C) (C1 := C1) (K := K) (ΘK := ΘK) (Δ := Δ) (d := d)
    (Vz := suzukiVProduct S z) (B0 := B0)
    (Bmid :=
      suzukiVProduct S z *
          (finiteSourceLayer 1 β N s +
            (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (s - 1) /
              Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)) +
        C * Real.exp (Real.sqrt K) * suzukiVProduct S z *
          (Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in s..σ,
              qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 *
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ s /
              Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)))
    hH hN2 hbase hcube hdom hcaseITau hz hcaseI hEndpoint
    (ne_of_gt (suzukiVProduct_pos S z)) hnu
    (by intro p hp; exact (suzukiVProduct_pos S p).le)
    hC hlog
    (by
      intro p hp
      simp only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] at hp
      exact hCeilFull p hp.1.1 hp.2.1 hp.2.2)
    hSourceDomain hClaim14_6_i hErrorDomain hIH
  rw [show suzukiSupportedBelow S z =
    S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl, hCarrier]
  exact hConcrete

end MathlibNt.SieveTheory
