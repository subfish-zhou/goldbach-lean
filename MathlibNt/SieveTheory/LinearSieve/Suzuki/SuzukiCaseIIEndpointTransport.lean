import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFromCaseI
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceFiniteAssembly

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The explicit `Σ₁₁` endpoint loss left by the Case-I estimate at the cubic
endpoint `β+1=3`. -/
noncomputable def caseIIEndpointSigma11
    (K : ℝ) (N : ℕ) (D σ : ℝ) : ℝ :=
  (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 /
    Real.log (D ^ (1 / σ))) * (3 / 3)

/-- The complete transported `q_D` contribution left by the Case-I estimate at
`β+1=3`. -/
noncomputable def caseIIEndpointQD
    (H : Section13HatLayers) (N : ℕ) (D d Δ σ C K : ℝ) : ℝ :=
  C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
    ((1 / 3) * (∫ t in (3 : ℝ)..σ,
      qD H (ErrorSign.ofDepth N).opposite D d Δ t) +
      (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ 3 /
        Real.log (D ^ (1 / σ))) * (3 / 3))

/-- The named, fully explicit endpoint error used by source-native Case II.
Besides the transported `B₀`, `Σ₁₁`, and `q_D` terms, it displays separately
the excess from the dimension-one product ratio:
`(3/s) * (K/log y) * finiteSourceLayer ...`. -/
noncomputable def caseIIEndpointErr
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D y z : ℕ) (d Δ σ C K B0 s : ℝ) : ℝ :=
  B0 + suzukiVProduct S (z : ℝ) *
    ((3 / s) * (K / Real.log (y : ℝ)) * finiteSourceLayer 1 2 N 3 +
      ((3 / s) * (1 + K / Real.log (y : ℝ))) *
        caseIIEndpointSigma11 K N (D : ℝ) σ +
      ((3 / s) * (1 + K / Real.log (y : ℝ))) *
        caseIIEndpointQD H N (D : ℝ) d Δ σ C K)

/-- At odd depth, the endpoint value of the finite source layer is
nonnegative on its exact parity domain. -/
theorem caseII_finiteSourceLayer_three_nonneg {N : ℕ} (hN : Odd N) :
    0 ≤ finiteSourceLayer 1 2 N 3 := by
  apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) N
  have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
  simp [KappaOneModel.parityDomain, hmod]
  norm_num

/-- The explicit `Σ₁₁` endpoint loss is nonnegative in the Case-II range. -/
theorem caseIIEndpointSigma11_nonneg {N D : ℕ} {K σ : ℝ}
    (hN : Odd N) (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ)) :
    0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ := by
  have hFprev : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
    have hprev : (N - 1) % 2 = 0 := by omega
    simp [KappaOneModel.parityDomain, hprev]
  have hlogw : 0 < Real.log ((D : ℝ) ^ (1 / σ)) :=
    Real.log_pos (by linarith)
  unfold caseIIEndpointSigma11
  positivity

/-- The transported `q_D` endpoint contribution is nonnegative under the
Section-13 positivity contract and the Case-II endpoint hypotheses. -/
theorem caseIIEndpointQD_nonneg
    {H : Section13HatLayers} {N D : ℕ} {d Δ σ C K : ℝ}
    (hH : Section13HatContract H 2) (hD : 1 < (D : ℝ))
    (h3σ : 3 ≤ σ) (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ)) (hC : 0 ≤ C) :
    0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
  have hqnonneg : ∀ t ∈ Set.Icc (3 : ℝ) σ,
      0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t := by
    intro t ht
    rcases ht with ⟨ht3, _htσ⟩
    exact (qD_pos H (ErrorSign.ofDepth N).opposite hD (by linarith)
      (hH.positive (ErrorSign.ofDepth N).opposite (t - 1) (by linarith))).le
  have hint : 0 ≤ ∫ t in (3 : ℝ)..σ,
      qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t :=
    intervalIntegral.integral_nonneg h3σ hqnonneg
  have hq3 : 0 ≤ qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ 3 :=
    (qD_pos H (ErrorSign.ofDepth N).opposite hD (by norm_num)
      (hH.positive (ErrorSign.ofDepth N).opposite (3 - 1) (by norm_num))).le
  have hlogw : 0 < Real.log ((D : ℝ) ^ (1 / σ)) :=
    Real.log_pos (by linarith)
  unfold caseIIEndpointQD
  positivity

/-- The genuine dimension-one finite Euler-product transport from `y` to `z`.
No independent product-ratio hypothesis is used. -/
theorem suzukiVProduct_le_dimensionOne_ratio
    (S : BoundingSieve) {K : ℝ} {y z : ℕ}
    (hy2 : 2 ≤ (y : ℝ)) (hyz : y ≤ z)
    (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiVProduct S (y : ℝ) ≤
      suzukiVProduct S (z : ℝ) *
        (Real.log (z : ℝ) / Real.log (y : ℝ)) *
        (1 + K / Real.log (y : ℝ)) := by
  have hyzR : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  have hratio := hlocal (y : ℝ) (z : ℝ) hy2 hyzR
  have hprod : suzukiVProduct S (y : ℝ) =
      suzukiVProduct S (z : ℝ) * suzukiLocalRatio S (y : ℝ) (z : ℝ) := by
    rcases hyz.eq_or_lt with rfl | hyzlt
    · have hempty : S.prodPrimes.primeFactors.filter
          (fun p : ℕ => (y : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (y : ℝ)) = ∅ := by
        ext p
        simp
      rw [suzukiLocalRatio, hempty]
      simp
    · symm
      have hyzltR : (y : ℝ) < (z : ℝ) := by exact_mod_cast hyzlt
      rw [suzukiVProduct_mul_localRatio_eq_sourceDiscreteEuler S hyzltR]
      unfold sourceDiscreteEuler suzukiVProduct suzukiSupportedBelow
      congr 1
      ext q
      simp
  rw [hprod]
  simpa [suzukiLocalRatio, mul_assoc] using
    (mul_le_mul_of_nonneg_left hratio (suzukiVProduct_pos S (z : ℝ)).le)

/-- The Case-II logarithmic ratio follows from the two exact power coordinates. -/
theorem caseII_log_ratio_of_power_identities
    {D y z s : ℝ} (hD : Real.exp 1 ≤ D) (hs : 0 < s)
    (hy : y = D ^ (1 / 3 : ℝ)) (hz : z = D ^ (1 / s)) :
    Real.log z / Real.log y = 3 / s := by
  have hDpos : 0 < D := (Real.exp_pos 1).trans_le hD
  have hDgt1 : 1 < D := by
    have hexp : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    simpa using hexp.trans_le hD
  have hlogD : 0 < Real.log D := Real.log_pos hDgt1
  have hlogy : Real.log y = (1 / 3 : ℝ) * Real.log D := by
    rw [hy, Real.log_rpow hDpos]
  have hlogz : Real.log z = (1 / s) * Real.log D := by
    rw [hz, Real.log_rpow hDpos]
  rw [hlogz, hlogy]
  field_simp

/-- Algebraic endpoint transport.  The Case-I main layer is split into the
required `(3/s)` term and the explicit ratio excess; every other Case-I term is
placed in `caseIIEndpointErr`. -/
theorem caseII_endpoint_transport_explicit
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {d Δ σ C K B0 s : ℝ}
    (hs : 0 < s)
    (hlogRatio : Real.log (z : ℝ) / Real.log (y : ℝ) = 3 / s)
    (hVratio : suzukiVProduct S (y : ℝ) ≤
      suzukiVProduct S (z : ℝ) *
        (Real.log (z : ℝ) / Real.log (y : ℝ)) *
        (1 + K / Real.log (y : ℝ)))
    (hF : 0 ≤ finiteSourceLayer 1 2 N 3)
    (hSigma11 : 0 ≤ caseIIEndpointSigma11 K N (D : ℝ) σ)
    (hQD : 0 ≤ caseIIEndpointQD H N (D : ℝ) d Δ σ C K)
    (hcaseI :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        B0 + suzukiVProduct S (y : ℝ) *
          (finiteSourceLayer 1 2 N 3 + caseIIEndpointSigma11 K N (D : ℝ) σ) +
          suzukiVProduct S (y : ℝ) *
            caseIIEndpointQD H N (D : ℝ) d Δ σ C K) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
      suzukiVProduct S (z : ℝ) * ((3 / s) * finiteSourceLayer 1 2 N 3) +
        caseIIEndpointErr S H N D y z d Δ σ C K B0 s := by
  rw [hlogRatio] at hVratio
  have hmain := mul_le_mul_of_nonneg_right hVratio hF
  have h11 := mul_le_mul_of_nonneg_right hVratio hSigma11
  have hq := mul_le_mul_of_nonneg_right hVratio hQD
  unfold caseIIEndpointErr
  calc
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D y) ≤
        B0 + suzukiVProduct S (y : ℝ) * finiteSourceLayer 1 2 N 3 +
          suzukiVProduct S (y : ℝ) * caseIIEndpointSigma11 K N (D : ℝ) σ +
          suzukiVProduct S (y : ℝ) * caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
      nlinarith [hcaseI]
    _ ≤ B0 +
        (suzukiVProduct S (z : ℝ) * (3 / s) *
          (1 + K / Real.log (y : ℝ))) * finiteSourceLayer 1 2 N 3 +
        (suzukiVProduct S (z : ℝ) * (3 / s) *
          (1 + K / Real.log (y : ℝ))) * caseIIEndpointSigma11 K N (D : ℝ) σ +
        (suzukiVProduct S (z : ℝ) * (3 / s) *
          (1 + K / Real.log (y : ℝ))) * caseIIEndpointQD H N (D : ℝ) d Δ σ C K := by
      gcongr
    _ = suzukiVProduct S (z : ℝ) * ((3 / s) * finiteSourceLayer 1 2 N 3) +
        (B0 + suzukiVProduct S (z : ℝ) *
          ((3 / s) * (K / Real.log (y : ℝ)) * finiteSourceLayer 1 2 N 3 +
            ((3 / s) * (1 + K / Real.log (y : ℝ))) *
              caseIIEndpointSigma11 K N (D : ℝ) σ +
            ((3 / s) * (1 + K / Real.log (y : ℝ))) *
              caseIIEndpointQD H N (D : ℝ) d Δ σ C K)) := by ring

/-- Final source-native Case-II converter.  It invokes the concrete Case-I
endpoint theorem at `y`, proves the `V(y)/V(z)` transport from the genuine
local-product hypothesis, discharges all three endpoint nonnegativity facts
from the parity domain and Section-13 positivity contract, and feeds the
resulting named `caseIIEndpointErr` directly to the source-native Case-II
assembly.  In particular, there is no arbitrary `hendpoint`, `hF`, `hSigma11`,
or `hQD` premise. -/
theorem caseII_total_le_from_caseI_endpoint_explicit
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
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hd : 0 ≤ d)
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
          ((K * 3 ^ 2 / (2 - 1)) *
            errorEnvelope H N (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ)) := by
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
    hH hN hN2 hycube (by convert hpower using 1 <;> norm_num) hyDhalf
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
    convert hcaseIRaw using 1 <;>
      simp only [caseIIEndpointSigma11, caseIIEndpointQD] <;> ring
  have hVratio := suzukiVProduct_le_dimensionOne_ratio S hy2 hyz hlocal
  have hlogRatio : Real.log (z : ℝ) / Real.log (y : ℝ) = 3 / s :=
    caseII_log_ratio_of_power_identities hD hs hpower.symm hz
  have hendpoint := caseII_endpoint_transport_explicit S H hs hlogRatio hVratio
    hF hSigma11 hQD hcaseI
  exact caseII_total_le_concrete_finiteSourceLayer_add_errorEnvelope
    S H hH hN hD hd hΔ0 hΔ1 hs hs3 (by linarith) hyz hyLower hyUpper hz hz2
    hlocal hendpoint


end MathlibNt.SieveTheory
