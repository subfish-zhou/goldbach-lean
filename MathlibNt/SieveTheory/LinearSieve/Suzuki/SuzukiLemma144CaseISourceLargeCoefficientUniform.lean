import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIICubicClosedEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeilClosed
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne
open SwitchingPrinciple.SuzukiLemma144KappaOne.Section13QhatMajorantClosure

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Case-I source-large coefficient and uniform `Σ₁₂` interface

The coefficient cutoff and the Claim-14.6 cutoff are selected before the later
Case-I constants.  In particular, the `Σ₁₂` theorem below has `C` and `K`
inside the universal quantifier following `D₀`; its API contains no post-`K`
eventual quantifier.
-/

/-- Quantitative source-large replacement for
`eventually_caseISourceOrderCoefficient_le_sameC_gap`.
The witness `C1min` is selected before `C1,K,D,A`. -/
theorem exists_caseISourceOrderCoefficient_sourceLargeLog_uniform
    {Amax d Δ Θ : ℝ}
    (hAmax : 0 ≤ Amax) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) (hΘ : 0 < Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K D A : ℝ), C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        0 ≤ A → A ≤ Amax → C1 * K ^ Θ < Real.log D →
        ∃ q : Lemma144StrictFactor,
          q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
          caseISourceOrderCoefficient A D d ≤ 1 - q.ρ := by
  have hev := eventually_caseISourceOrderCoefficient_le_sameC_gap
    hAmax hΔ0 hΔ1 hd
  obtain ⟨Dpre, hpre⟩ := eventually_atTop.1 hev
  let Dcut : ℝ := max Dpre (Real.exp (Real.exp 1))
  let C1min : ℝ := max 1 (Real.log Dcut)
  have hDcut0 : 0 < Dcut :=
    (Real.exp_pos (Real.exp 1)).trans_le (le_max_right _ _)
  have hC1min1 : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, hC1min1, ?_⟩
  intro C1 K D A hC1 hK hD2 hA hAAmax hlarge
  have hK0 : 0 < K := by linarith
  have hKpow1 : 1 ≤ K ^ Θ := Real.one_le_rpow (by linarith) hΘ.le
  have hC11 : 1 ≤ C1 := hC1min1.trans hC1
  have hbudget : C1min ≤ C1 * K ^ Θ := by
    calc
      C1min ≤ C1 := hC1
      _ = C1 * 1 := by ring
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left hKpow1 (by linarith)
  have hlogcut : Real.log Dcut < Real.log D :=
    (le_max_right 1 (Real.log Dcut)).trans_lt (hbudget.trans_lt hlarge)
  have hD0 : 0 < D := by linarith
  have hcutD : Dcut < D := by
    have he := Real.exp_lt_exp.mpr hlogcut
    rw [Real.exp_log hDcut0, Real.exp_log hD0] at he
    exact he
  obtain ⟨q, hq, hcoefMax⟩ :=
    hpre D ((le_max_left Dpre (Real.exp (Real.exp 1))).trans hcutD.le)
  have hlogD_exp : Real.exp 1 < Real.log D := by
    have hcutExp : Real.exp (Real.exp 1) ≤ Dcut := le_max_right _ _
    have hExpD : Real.exp (Real.exp 1) < D := hcutExp.trans_lt hcutD
    exact (Real.lt_log_iff_exp_lt hD0).2 hExpD
  have hll : 0 < Real.log (Real.log D) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans hlogD_exp)
  have hd0 : 0 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hΔ1
    have : 0 < 7 / (1 - Δ) := div_pos (by norm_num) hden
    linarith
  have hlog27 : 1 < Real.log (27 * D) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * D)).2
    nlinarith [Real.exp_one_lt_d9]
  have hsigma : 0 < sourceSigma D d := by
    unfold sourceSigma
    exact mul_pos (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _)
      (Real.log_pos hlog27)
  have hden : 0 < Real.log (Real.log D) * sourceSigma D d := mul_pos hll hsigma
  refine ⟨q, hq, ?_⟩
  unfold caseISourceOrderCoefficient at hcoefMax ⊢
  calc
    A / (Real.log (Real.log D) * sourceSigma D d) ≤
        Amax / (Real.log (Real.log D) * sourceSigma D d) :=
      (div_le_div_iff_of_pos_right hden).2 hAAmax
    _ ≤ 1 - q.ρ := hcoefMax

/-- Under the common scale `C ≥ A*C145`, the direct `Σ₀` coefficient is
bounded before `C145` and `C` are chosen. -/
theorem caseISigmaZero_ratio_le_commonScale
    {A C C145 : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hscale : A * C145 ≤ C) :
    C145 / C ≤ 1 / A := by
  rw [div_le_div_iff₀ hC hA]
  nlinarith

/-- The three endpoint constants have a fixed upper bound under the common
scale `C ≥ max 3 (A*C145)`.  This is the `Amax` supplied to the quantitative
source-order theorem above. -/
theorem caseI_endpointCoefficient_le_commonScale
    {A C C145 K L R : ℝ}
    (hA : 0 < A) (hC3 : 3 ≤ C) (hscale : A * C145 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) :
    C145 / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R ≤
      1 / A + 2 * L * R + 12 * R := by
  have hC : 0 < C := by linarith
  have hzero := caseISigmaZero_ratio_le_commonScale hA hC hscale
  have hexp : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg K)
  have hden : 0 < C * Real.exp (Real.sqrt K) := mul_pos hC (Real.exp_pos _)
  have hden3 : 3 ≤ C * Real.exp (Real.sqrt K) := by nlinarith
  have hmid : 6 * L * R / (C * Real.exp (Real.sqrt K)) ≤ 2 * L * R := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hL hR]
  linarith

/-- The natural-ceiling `Σ₁₂` same-constant contraction with one Claim-14.6
cutoff selected before the varying sieve `S`, then before `C`, `K`, the depth
`N`, and the coordinate `s`.  The threshold is genuinely source-uniform: it is
the Claim-14.6 cutoff, which depends only on `H`, `d`, and `Δ`. -/
theorem exists_sigmaTwelve_internal_contraction_binderUniform_in_S
    {H : Section13HatLayers}
    {d Δ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ D₀ : ℝ, 1 < D₀ ∧
      ∀ S : BoundingSieve,
      ∀ (C K : ℝ), 2 ≤ K → HasDimensionOneLocalProductBound S K → 0 ≤ C →
      ∀ (D N : ℕ) (s : ℝ) (z : ℕ), D₀ ≤ (D : ℝ) →
      0 < s →
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      1 < sourceSigma (D : ℝ) d →
      s ≤ sourceSigma (D : ℝ) d →
      1 < (D : ℝ) →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s) →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        Claim14_13PointwisePremise H N (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ) / 2 ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ *
              sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          q.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) := by
  obtain ⟨D₀, hD₀, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  refine ⟨D₀, hD₀, ?_⟩
  intro S C K hK hlocal hC D N s z hDlarge hs0 hsLower hσ1 hsσ hD hv2 hw2 hwv hz
    hthreshold hCeil hT h1413
  obtain ⟨_hi, hii, hiii⟩ := h146 (D : ℝ) hDlarge
  let σ : ℝ := sourceSigma (D : ℝ) d
  let a : ℝ := sigma12ContractionMultiplier σ Δ
  let A : ℝ := C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
    (Real.log (D : ℝ)) ^ (-Δ)
  let B : ℝ := errorEnvelope H N (D : ℝ) d s
  let R : ℝ := (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
      (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s)
  have h12 := sigmaTwelve_suzukiVProduct_le_qD_lemma8_7_natCeil_closed
    (S := S) (H := H) (β := (2 : ℝ)) (C := C) (K := K) (d := d) (Δ := Δ)
    (w := (D : ℝ) ^ (1 / σ)) (v := (D : ℝ) ^ (1 / s))
    (s := s) (τ := s) (σ := σ) (N := N) (D := D) (znat := z)
    hH.toSection13HatContract hD hv2 hw2 hwv le_rfl hz rfl rfl
    hthreshold hsσ hK hlocal (by simpa [σ] using hii) hC hΔ0.le
    (by simpa [σ] using hCeil) (by simpa [σ] using hT) (by simpa [σ] using h1413)
  have hint := hiii (ErrorSign.ofDepth N) s hsLower hsσ
  have hintScaled :
      (1 / s) * (∫ t in s..σ,
        qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤ a * B := by
    have hmul := mul_le_mul_of_nonneg_left hint.le (one_div_nonneg.mpr hs0.le)
    calc
      (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) ≤
          (1 / s) * (a * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by
            simpa [σ, a, sigma12ContractionMultiplier] using hmul
      _ = a * ((1 / s) * lambda H (ErrorSign.ofDepth N) (D : ℝ) d 0 s) := by ring
      _ = a * B := by rw [one_div_mul_lambda_eq_errorEnvelope H hs0]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.exp_nonneg _)) (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hD.le) _)
  have hraw :
      sigmaTwelve S.prodPrimes.primeFactors S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ N D σ s ≤
        a * (A * B) + A * R := by
    apply h12.trans
    rw [show C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
        ((Real.log (D : ℝ)) ^ (-Δ) *
          ((1 / s) * (∫ t in s..σ,
            qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) +
            (6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite
              (D : ℝ) d Δ s / Real.log ((D : ℝ) ^ (1 / σ))) * (s / s))) =
        A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) by
            dsimp [A, R]; ring]
    have hinside :
        (1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R ≤
          a * B + R := add_le_add hintScaled (le_refl R)
    calc
      A * ((1 / s) * (∫ t in s..σ,
          qD H (ErrorSign.ofDepth N).opposite (D : ℝ) d Δ t) + R) ≤
          A * (a * B + R) := mul_le_mul_of_nonneg_left hinside hA
      _ = a * (A * B) + A * R := by ring
  obtain ⟨q, hq, haq⟩ := exists_sigma12_sameC_strictFactor hσ1 hΔ1
  have hB : 0 ≤ B := by
    apply errorEnvelope_nonneg H N hD hs0.le
    exact (hH.positive (ErrorSign.ofDepth N) s hs0).le
  have hbudget : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨q, by simpa [σ] using hq, ?_, ?_⟩
  · simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hraw
  · have hρ : a ≤ q.ρ := haq.le
    have hslack : a * (A * B) + A * R ≤ q.ρ * (A * B) + A * R := by
      exact add_le_add (mul_le_mul_of_nonneg_right hρ hbudget) le_rfl
    have hfinal := hraw.trans hslack
    simpa [σ, a, A, B, R, sigma12InheritedBudget,
      sigma12EndpointRemainder, mul_assoc] using hfinal

/-- Compatibility specialization of the threshold-uniform-in-`S` contraction. -/
theorem exists_sigmaTwelve_internal_contraction_binderUniform
    {S : BoundingSieve} {H : Section13HatLayers}
    {d Δ : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ D₀ : ℝ, 1 < D₀ ∧
      ∀ (C K : ℝ), 2 ≤ K → HasDimensionOneLocalProductBound S K → 0 ≤ C →
      ∀ (D N : ℕ) (s : ℝ) (z : ℕ), D₀ ≤ (D : ℝ) →
      0 < s →
      2 + (ErrorSign.ofDepth N).epsilon ≤ s →
      1 < sourceSigma (D : ℝ) d →
      s ≤ sourceSigma (D : ℝ) d →
      1 < (D : ℝ) →
      2 ≤ (D : ℝ) ^ (1 / s) →
      2 ≤ (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) →
      (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (D : ℝ) ^ (1 / s) →
      z = ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      H.betaHat + (ErrorSign.ofDepth N).epsilon ≤ s →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) → 2 ≤ p ∧ 2 * p ≤ D) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p)) →
      (∀ p ∈ S.prodPrimes.primeFactors,
        (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ) →
        (p : ℝ) < (D : ℝ) ^ (1 / s) →
        Claim14_13PointwisePremise H N (D : ℝ) d Δ
          (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ))) →
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ) / 2 ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          sigma12ContractionMultiplier (sourceSigma (D : ℝ) d) Δ *
              sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) ∧
        sigmaTwelve S.prodPrimes.primeFactors S.nu
            (fun p => suzukiVProduct S (p : ℝ))
            (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
            (suzukiVProduct S (z : ℝ)) C K Δ N D
            (sourceSigma (D : ℝ) d) s ≤
          q.ρ * sigma12InheritedBudget S H N D z C K d Δ s +
            sigma12EndpointRemainder S H N D z C K d Δ s
              (sourceSigma (D : ℝ) d) := by
  obtain ⟨D₀, hD₀, hall⟩ :=
    exists_sigmaTwelve_internal_contraction_binderUniform_in_S hH hd1 hΔ0 hΔ1
  exact ⟨D₀, hD₀, hall S⟩


end MathlibNt.SieveTheory
