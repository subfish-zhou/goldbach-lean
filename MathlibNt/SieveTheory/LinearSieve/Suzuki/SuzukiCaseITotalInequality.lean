import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigma11Sigma12MiddleRange
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiErrorEnvelopeCeilBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIEndpointRegime

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- Production source-correct Case-I assembly of `Σ₀ + Σ₁₁ + Σ₁₂` for the
Section-13 error envelope.

The source recurrence is supplied directly by
`suzukiSourceParitySum_recurrence_caseI_two_ranges`; the `Σ₀` estimate is
transported directly from the explicit Claim-14.5 endpoint provider at `s'=σ`.
The recursive input is the literal natural-ceiling induction hypothesis and is
transported only through the proved ceiling bridge.  The source-layer comparison
is derived from Proposition 9.3 using the explicit parity-domain hypotheses,
and the error comparison from recursive Claim 14.6(i). -/
theorem caseI_total_le_sigma0_add_sigma11_add_sigma12
    (S : BoundingSieve) (V : ℕ → ℝ) (H : Section13HatLayers)
    {N D z : ℕ} {β σ s C C1 K ΘK Δ d Vz B0 Bmid : ℝ}
    (hH : Section13HatContract H β)
    (hN2 : 2 ≤ N)
    (hbase : Odd N → suzukiSourceV S 1 D z = 0)
    (hcube : ∀ n ∈ sourceParityIndices N, 2 ≤ n → Odd n →
      ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D)
    (hdom : CaseIThreeRangeDomain D z σ s)
    (hτ : caseITau (D : ℝ) s = s)
    (hz : (D : ℝ) ^ (1 / s) = (z : ℝ))
    (hcaseI : Claim14_5CaseI β N s σ)
    (hEndpoint : Claim14_5Regime β (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hVz : Vz ≠ 0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      0 ≤ S.nu p)
    (hV : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      0 ≤ V p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hCeil : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      2 ≤ p ∧ 2 * p ≤ D)
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1))
    (hClaim : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ s,
      inheritedCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S z)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      V (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ s)
    (hMiddle87 :
      sigmaEleven (suzukiSupportedBelow S z) S.nu V Vz β N D σ s +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu V
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          Vz C K Δ N D σ s ≤
      Bmid) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤ B0 + Bmid := by
  let support := suzukiSupportedBelow S z
  let T : ℕ → ℕ → ℕ → ℝ := fun n D' p =>
    ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p
  have hSource : ∀ p ∈ sigmaOneCarrier support D σ s,
      finiteSourceLayer 1 β (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 β (N - 1) (inheritedCoordinate D p) := by
    intro p hp
    exact finiteSourceLayer_recursive_le_inherited hH.beta_gt_one (N - 1) D p
      (hCeil p (by simpa [support] using hp)).1
      (hCeil p (by simpa [support] using hp)).2
      (hSourceDomain p (by simpa [support] using hp)).1
      (hSourceDomain p (by simpa [support] using hp)).2
  have hIHsource : PointwiseInductionContract support T V
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ s :=
    naturalCeilContract_to_sourceCoordinate_errorEnvelope_of_claim14_6
      support T V H β C K Δ d N D σ s hH
      (by simpa [support] using hV) hC (by simpa [support] using hlog)
      hSource (by simpa [support] using hCeil)
      (by simpa [support] using hClaim)
      (by simpa [support] using hErrorDomain)
      (by simpa [support, T] using hIH)
  have h14 : sigmaOne support S.nu T N D σ s ≤
      sigmaEleven support S.nu V Vz β N D σ s +
        sigmaTwelve support S.nu V
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          Vz C K Δ N D σ s :=
    equation14_10_finset_assembly support S.nu V T
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      Vz β C K Δ N D σ s
      hVz (by simpa [support] using hnu) hIHsource
  have hRec :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
        (∑ p ∈ (suzukiSupportedBelow S z).filter
            (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
          S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
            suzukiSourceV S m (D ⌈/⌉ p) p)) +
        (∑ p ∈ (suzukiSupportedBelow S z).filter
            (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
              (p : ℝ) < (D : ℝ) ^ (1 / s)),
          S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
            suzukiSourceV S m (D ⌈/⌉ p) p)) := by
    simpa [hτ] using
      (suzukiSourceParitySum_recurrence_caseI_two_ranges S
        hN2 hbase hcube hdom hτ hz)
  have hSigma0 := caseI_sigma0_le_of_claim14_5_sigma_endpoint S
    hdom hτ hz hcaseI
    (fun p => S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
      suzukiSourceV S m (D ⌈/⌉ p) p)) hEndpoint
  rw [hRec]
  have h1 :
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
            (p : ℝ) < (D : ℝ) ^ (1 / s)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ Bmid := by
    change sigmaOne support S.nu T N D σ s ≤ Bmid
    exact h14.trans (by simpa [support] using hMiddle87)
  exact add_le_add hSigma0 h1


end MathlibNt.SieveTheory
