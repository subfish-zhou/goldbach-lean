import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIConcreteFiniteAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIEndpointRegime

open scoped Classical BigOperators
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- A literal cubic carrier makes the source base layer vanish.  This is the
exact finite statement needed when the Case-I theorem is used at the Case-II
cutoff; no global hypothesis `y^N ≤ D` is involved. -/
theorem suzukiSourceV_one_eq_zero_of_supported_cube
    (S : BoundingSieve) {D y : ℕ}
    (hcube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D) :
    suzukiSourceV S 1 D y = 0 := by
  classical
  rw [suzukiSourceV_one]
  apply sum_eq_zero
  intro p hp
  have hp' := mem_filter.mp hp
  exact False.elim ((Nat.not_lt_of_ge hp'.2) (hcube p hp'.1))

/-- At `s = β+1`, the finite correction in `caseITau` is inactive under the
same explicit large-`D` logarithmic threshold as in Case I. -/
theorem caseITau_eq_beta_add_one_of_log_threshold
    {β D : ℝ} (hβ : 1 < β) (hD : 1 < D)
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log D) :
    caseITau D (β + 1) = β + 1 :=
  caseITau_eq_s_of_log_threshold hβ (by linarith) hD hDlarge

/-- Maximal direct instantiation of the final concrete Case-I theorem at the
Case-II endpoint `s=β+1`, `z=y` (odd `N`).

The Case-I-only premises `hbase`, `hcube`, `hdom`, `hcaseITau`, `hcaseI`,
`hsdom`, `hsm1dom`, `hv2`, and `hvz` are discharged here.  The endpoint
provider remains at `s'=σ`, not at the current endpoint `β+1`; hence the theorem
does not hide the desired current-`s` estimate in `hEndpoint`.

Two genuinely arithmetic endpoint facts remain explicit: the exact real power
identity `D^(1/(β+1))=y` required by the Case-I API, and `y ≤ D/2`, required by
its exact `min(y,D/2)` cutoff contract. -/
theorem caseII_endpoint_le_concrete_finiteSourceLayer_add_qD
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y : ℕ} {β σ C C1 K ΘK Δ d B0 : ℝ}
    (hH : Section13HatContract H β)
    (hN : Odd N) (hN2 : 2 ≤ N)
    (hycube : ∀ p ∈ suzukiSupportedBelow S y, p ^ 3 < D)
    (hpower : (D : ℝ) ^ (1 / (β + 1)) = (y : ℝ))
    (hyDhalf : (y : ℝ) ≤ (D : ℝ) / 2)
    (hβ1σ : β + 1 ≤ σ)
    (hD : 1 < (D : ℝ))
    (hDlarge : β * Real.log 2 ≤ (β - 1) * Real.log (D : ℝ))
    (hwy : (D : ℝ) ^ (1 / σ) ≤ (y : ℝ))
    (hy2 : 2 ≤ (y : ℝ))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hEndpoint : Claim14_5Regime β (D : ℝ) σ C1 K ΘK σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤ B0)
    (hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ (β + 1),
      0 ≤ S.nu p)
    (hC : 0 ≤ C)
    (hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ (β + 1),
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ))
    (hSourceDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain β (N - 1))
    (hClaim14_6_i : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      Claim14_6_MonotoneLambdaPremise H ((D ⌈/⌉ p : ℕ) : ℝ) d σ)
    (hErrorDomain : ∀ p ∈ sigmaOneCarrier
        (suzukiSupportedBelow S y) D σ (β + 1),
      inheritedCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ ∧
      recursiveCoordinate D p ∈
          Set.Icc (H.betaHat + (ErrorSign.ofDepth (N - 1)).epsilon) σ)
    (hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      β C K Δ N D σ (β + 1))
    (hErrorThreshold :
      H.betaHat + (ErrorSign.ofDepth N).epsilon < β + 1)
    (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hClaim14_6_ii : Claim14_6_MonotoneQPremise H (D : ℝ) d Δ σ)
    (hΔ : 0 ≤ Δ)
    (hCeilFull : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (y : ℝ) → 2 ≤ p ∧ 2 * p ≤ D)
    (hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (y : ℝ) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p))
    (hClaim14_13 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (y : ℝ) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
      B0 +
        (suzukiVProduct S y *
            (finiteSourceLayer 1 β N (β + 1) +
              (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) β /
                Real.log ((D : ℝ) ^ (1 / σ))) * ((β + 1) / (β + 1))) +
          C * Real.exp (Real.sqrt K) * suzukiVProduct S y *
            (Real.log (D : ℝ)) ^ (-Δ) *
            ((1 / (β + 1)) * (∫ t in (β + 1)..σ,
                qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
              (6 * K ^ 2 *
                  qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ (β + 1) /
                Real.log ((D : ℝ) ^ (1 / σ))) *
                  ((β + 1) / (β + 1)))) := by
  have hτ : caseITau (D : ℝ) (β + 1) = β + 1 :=
    caseITau_eq_beta_add_one_of_log_threshold hH.beta_gt_one hD hDlarge
  have hdom : CaseIThreeRangeDomain D y σ (β + 1) := by
    constructor
    · rw [hτ]
      exact hwy.trans_eq hpower.symm
    · rw [hτ, hpower, min_eq_left hyDhalf]
  have hcaseI : Claim14_5CaseI β N (β + 1) σ := by
    unfold Claim14_5CaseI
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    constructor
    · norm_num [hmod]
    · exact hβ1σ
  have hsdom : β + 1 ∈ KappaOneModel.parityDomain β N := by
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    simp only [KappaOneModel.parityDomain, hmod, if_pos, Set.mem_Ioi]
    linarith
  have hNm1mod : (N - 1) % 2 = 0 := by
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hsm1dom : β + 1 - 1 ∈ KappaOneModel.parityDomain β (N - 1) := by
    simp [KappaOneModel.parityDomain, hNm1mod]
  have hresult := caseI_total_le_concrete_finiteSourceLayer_add_qD
    (S := S) (H := H) (N := N) (D := D) (z := y)
    (β := β) (σ := σ) (s := β + 1) (C := C) (C1 := C1)
    (K := K) (ΘK := ΘK) (Δ := Δ) (d := d) (B0 := B0)
    hH hN2
    (fun _ => suzukiSourceV_one_eq_zero_of_supported_cube S hycube)
    (fun _ _ _ _ p hp => hycube p hp)
    hdom hτ hpower hcaseI hEndpoint hnu hC hlog hSourceDomain
    hClaim14_6_i hErrorDomain hIH hsdom hsm1dom hD hy2
    (by rw [hpower]; exact hy2) hw2
    (hwy.trans_eq hpower.symm) hpower.le
    hErrorThreshold hK hlocal hClaim14_6_ii hΔ
    (by
      intro p hp hpw hpy
      exact hCeilFull p hp hpw (by simpa only [hpower] using hpy))
    (by
      intro p hp hpw hpy
      exact hT p hp hpw (by simpa only [hpower] using hpy))
    (by
      intro p hp hpw hpy
      exact hClaim14_13 p hp hpw (by simpa only [hpower] using hpy))
  simpa only [add_sub_cancel_right] using hresult


end MathlibNt.SieveTheory
