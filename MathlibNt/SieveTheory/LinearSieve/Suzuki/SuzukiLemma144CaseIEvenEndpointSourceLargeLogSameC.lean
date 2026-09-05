import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144RecursiveCoordinateSourceSigma
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144MovingDomainFiniteInduction
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIGeometryPacket
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSigmaTwelveCarrierEquality
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISuccessorFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0EndpointTransportUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma12NatCeilUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11EvenEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144EndpointSourceBoundsSourceLargeLogUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

theorem evenEndpoint_carrier_scale
    (S : BoundingSieve) {D Dmin : ℕ} {σ : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) :
    CarrierQuotientThresholdGeometry S.prodPrimes.primeFactors D Dmin σ 2 := by
  intro p hp
  have hp' := hp
  simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) := hp'.2.2
  have hsquareR : (p : ℝ) ^ (2 : ℕ) < (D : ℝ) := by
    have hiff := Real.lt_rpow_inv_iff_of_pos
      (x := (p : ℝ)) (y := (D : ℝ)) (z := (2 : ℝ))
      (by positivity) (by positivity) (by norm_num)
    norm_num [one_div] at hiff hpRoot ⊢
    exact hiff.mp hpRoot
  have hsquare : p ^ 2 < D := by exact_mod_cast hsquareR
  by_cases hminp : Dmin ≤ p
  · calc
      Dmin * p ≤ p * p := Nat.mul_le_mul_right p hminp
      _ = p ^ 2 := by ring
      _ ≤ D := Nat.le_of_lt hsquare
  · have hpmin : p < Dmin := Nat.lt_of_not_ge hminp
    calc
      Dmin * p ≤ Dmin * Dmin := Nat.mul_le_mul_left Dmin (Nat.le_of_lt hpmin)
      _ = Dmin ^ 2 := by ring
      _ ≤ D := hD

/-- Actual strict endpoint carriers allow the moving predecessor IH to be
instantiated without the illegal formal coordinate `1`. -/
theorem evenEndpoint_pointwiseContract_of_movingIH_sourceLargeConsumer
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (M D Dmin : ℕ)
    (hDmin : 2 ≤ Dmin) (hM : Even M) (hM2 : 2 ≤ M) (hD : 4 ≤ D)
    (hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D Dmin
        (sourceSigma (D : ℝ) d) 2)
    (hrecursiveSigma : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d)
    (hError : ∀ p ∈ sigmaOneCarrier
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊) D
        (sourceSigma (D : ℝ) d) 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p))
    (hC : 0 ≤ C)
    (hIH : Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) Dmin) :
    PointwiseInductionContract
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊)
      (suzukiActualT S) (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D (sourceSigma (D : ℝ) d) 2 := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hpkt := lemma144_caseI_even_endpoint_source_packet S hM hM2 hD (z := z) rfl
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp; exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hnatural : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S z) (suzukiActualT S)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ M D (sourceSigma (D : ℝ) d) 2 := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hpPrime := hprime p hpS
    have hqThreshold := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact hIH (D ⌈/⌉ p) p hqThreshold hq2 hpPrime.two_le
      (recursiveCoordinate D p) (hpkt p hpS).2.1
      (hrecursiveSigma p hp) (recursiveCoordinate_power_identity hpPrime.two_le hq2)
  apply naturalCeilContract_to_sourceCoordinate
    (suzukiSupportedBelow S z) (suzukiActualT S)
    (fun p => suzukiVProduct S p)
    (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    2 C K Δ M D (sourceSigma (D : ℝ) d) 2
  · intro p _; exact (suzukiVProduct_pos S p).le
  · exact hC
  · intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hqThreshold := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqThreshold
    exact (Real.log_pos (by exact_mod_cast (show 1 < D ⌈/⌉ p by omega))).le
  · intro p hp; exact (hpkt p (Finset.mem_filter.mp hp).1).2.2
  · exact hError
  · simpa [z] using hnatural

/-! Closed-left-endpoint source control used by the even Case-I producer. -/

private theorem finiteSourceLayer_continuousOn_closedDomain_even
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    ContinuousOn (finiteSourceLayer 1 β N) (KappaOneModel.closedDomain β N) := by
  classical
  unfold finiteSourceLayer
  induction Finset.Icc 1 N using Finset.induction_on with
  | empty => simpa using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) _)
  | @insert n u hn ih =>
      simp only [Finset.sum_insert hn]
      by_cases hpar : n % 2 = N % 2
      · simp only [hpar, if_true]
        have hclosed : KappaOneModel.closedDomain β n =
            KappaOneModel.closedDomain β N := by
          unfold KappaOneModel.closedDomain KappaOneModel.eps
          rw [hpar]
        have hreg := (KappaOneModel.regular hβ n).continuous
        rw [hclosed] at hreg
        exact (hreg.congr fun s _ =>
          (KappaOneModel.layer_eq_suzukiLayer β n s).symm).add ih
      · simp only [hpar, if_false]
        exact continuousOn_const.add ih

/-- The uniform Lemma-13.2 finite-layer estimate extends to the closed odd
predecessor endpoint by one-sided continuity. -/
theorem lemma132_finiteSourceLayer_evenEndpoint_uniform_sourceLargeConsumer
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ M : ℕ, Even M → 2 ≤ M →
      finiteSourceLayer 1 2 (M - 1) 1 ≤
        L * H.T (ErrorSign.ofDepth M).opposite 1 := by
  obtain ⟨L, hL, hmajor⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨L, hL, ?_⟩
  intro M hM hM2
  have hpred : (M - 1) % 2 = 1 := by
    have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
    omega
  have hMpred : 1 ≤ M - 1 := by omega
  let F : ℝ → ℝ := fun x => x * finiteSourceLayer 1 2 (M - 1) x
  let G : ℝ → ℝ := fun x => L * x ^ 2 * H.T (ErrorSign.ofDepth (M - 1)) x
  have hclosed : (1 : ℝ) ∈ KappaOneModel.closedDomain 2 (M - 1) := by
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    norm_num
  have hFC : ContinuousWithinAt F (KappaOneModel.closedDomain 2 (M - 1)) 1 := by
    apply continuousWithinAt_id.mul
    exact (finiteSourceLayer_continuousOn_closedDomain_even (by norm_num) (M - 1))
      1 hclosed
  have hGC : ContinuousAt G 1 := by
    dsimp [G]
    have hTcont := (hH.continuous (ErrorSign.ofDepth (M - 1))).continuousAt
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact (continuousAt_const.mul (continuousAt_id.pow 2)).mul hTcont
  have hsub : Set.Ioi (1 : ℝ) ⊆ KappaOneModel.closedDomain 2 (M - 1) := by
    intro x hx
    change (1 : ℝ) < x at hx
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    linarith
  have hFt : Tendsto F (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (F 1)) :=
    hFC.mono_left (nhdsWithin_mono 1 hsub)
  have hGt : Tendsto G (𝓝[Set.Ioi (1 : ℝ)] 1) (𝓝 (G 1)) :=
    hGC.tendsto.mono_left inf_le_left
  have hEventually : ∀ᶠ x in 𝓝[Set.Ioi (1 : ℝ)] 1, F x ≤ G x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxdom : x ∈ KappaOneModel.parityDomain 2 (M - 1) := by
      simp [KappaOneModel.parityDomain, hpred]
      norm_num
      exact hx
    exact hmajor (M - 1) x hMpred hxdom
  have hlim : F 1 ≤ G 1 := le_of_tendsto_of_tendsto hFt hGt hEventually
  dsimp [F, G] at hlim
  rw [ErrorSign.ofDepth_pred_eq_opposite (by omega : 1 ≤ M)] at hlim
  simpa using hlim

/-- Source-bound interface for the two endpoint remainders at even depth. -/
def CaseI1423EvenEndpointSourceBoundsSourceScalar
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ : ℝ) : Prop :=
  ∃ A11 A12 : ℝ, 0 ≤ A11 ∧ 0 ≤ A12 ∧
    ∀ (D M : ℕ), 3 ≤ D →
      K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
          Real.log (Real.log (D : ℝ)) /
          (Real.log (D : ℝ)) ^ (1 - Δ) ≤ 1 →
      Even M → 2 ≤ M → (2 : ℝ) ≤ sourceSigma (D : ℝ) d →
      let σ := sourceSigma (D : ℝ) d
      let z := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
      let B := sigma12InheritedBudget S H M D z C K d Δ 2
      suzukiVProduct S z *
          (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
            Real.log ((D : ℝ) ^ (1 / σ))) ≤
          A11 * caseI1423RemainderUnit B (D : ℝ) σ ∧
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
          A12 * caseI1423RemainderUnit B (D : ℝ) σ

/-! The proof below reuses the source-normalization algebra of (14.23); only
its finite-layer input is replaced by the closed endpoint lemma above. -/

private lemma evenEndpoint_sigma11_front
    (V K F logD σ : ℝ) (hlogD : 0 < logD) (hσ : 0 < σ) :
    V * (6 * K ^ 2 * F / (logD / σ)) =
      6 * V * (K ^ 2 * σ / logD) * F := by
  field_simp [ne_of_gt hlogD, ne_of_gt hσ]

private lemma evenEndpoint_sigma11_budget
    (L R C E V E0 logPow logLog σ : ℝ)
    (hC : 0 < C) (hE : 0 < E) (hll : 0 < logLog) (hσ : 0 < σ) :
    6 * L * R * V * E0 * (logPow / (logLog * σ)) =
      (6 * L * R / (C * E)) *
        (C * E * V * logPow * E0 / (logLog * σ)) := by
  field_simp [ne_of_gt hC, ne_of_gt hE, ne_of_gt hll, ne_of_gt hσ]

private lemma evenEndpoint_sigma11_normalization
    (K σ logσ logD logLog Δ : ℝ)
    (hlog : 0 < logD) (hll : 0 < logLog) (hσ : 0 < σ)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD ^ (1 - Δ))
    (hpowe : logD ^ (-Δ) * logD = logD ^ (1 - Δ)) :
    K ^ 2 * σ ^ 2 * logσ / logD ≤ logD ^ (-Δ) / (logLog * σ) := by
  apply (div_le_div_iff₀ hlog (mul_pos hll hσ)).2
  calc
    K ^ 2 * σ ^ 2 * logσ * (logLog * σ) =
        K ^ 2 * σ ^ 3 * logσ * logLog := by ring
    _ ≤ logD ^ (1 - Δ) := hscalar
    _ = logD ^ (-Δ) * logD := hpowe.symm

private lemma evenEndpoint_sigma12_algebra
    (q V K R σ logσ E0 logLog logD : ℝ)
    (hR : 0 ≤ R) (hσ : 0 < σ) (hE0 : 0 ≤ E0)
    (hV : 0 ≤ V) (hLogLog : 0 ≤ logLog)
    (hfront : V * q ≤ V * 2 * R * σ * logσ * E0)
    (hscalar : K ^ 2 * σ ^ 3 * logσ * logLog ≤ logD) :
    q * σ ^ 2 * V * 6 * K ^ 2 * logLog ≤ R * E0 * V * logD * 12 := by
  have hfactor : 0 ≤ 6 * K ^ 2 * logLog * σ ^ 2 := by positivity
  have hbudgetFactor : 0 ≤ 12 * R * E0 * V := by positivity
  calc
    q * σ ^ 2 * V * 6 * K ^ 2 * logLog =
        (6 * K ^ 2 * logLog * σ ^ 2) * (V * q) := by ring
    _ ≤ (6 * K ^ 2 * logLog * σ ^ 2) *
        (V * 2 * R * σ * logσ * E0) :=
      mul_le_mul_of_nonneg_left hfront hfactor
    _ = (12 * R * E0 * V) *
        (K ^ 2 * σ ^ 3 * logσ * logLog) := by ring
    _ ≤ (12 * R * E0 * V) * logD :=
      mul_le_mul_of_nonneg_left hscalar hbudgetFactor
    _ = R * E0 * V * logD * 12 := by ring

/-- Closed-endpoint source bounds with the source-uniform constants exposed.
This strengthened form is used by the pointwise source-large producer to choose
its coefficient cutoff before the later common constant and `K`. -/
theorem caseI1423EndpointSourceBounds_evenEndpoint_explicit
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ L R : ℝ)
    (hH : Section13HatSourceContract H) (hC : 0 < C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d)
    (hL : 1 ≤ L)
    (hfinite : ∀ M : ℕ, Even M → 2 ≤ M →
      finiteSourceLayer 1 2 (M - 1) 1 ≤
        L * H.T (ErrorSign.ofDepth M).opposite 1)
    (hR : 1 ≤ R)
    (hratio : ∀ (sign : ErrorSign) (s σ : ℝ), 2 ≤ s → s ≤ σ →
      proposition131iiiReverseRatio H sign s ≤
        R * (σ * Real.log (Real.exp 1 * σ))) :
    ∀ (D M : ℕ), 3 ≤ D →
        K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
            Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
            Real.log (Real.log (D : ℝ)) /
            (Real.log (D : ℝ)) ^ (1 - Δ) ≤ 1 →
        Even M → 2 ≤ M → (2 : ℝ) ≤ sourceSigma (D : ℝ) d →
        let σ := sourceSigma (D : ℝ) d
        let z := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
        let B := sigma12InheritedBudget S H M D z C K d Δ 2
        suzukiVProduct S z *
            (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
              Real.log ((D : ℝ) ^ (1 / σ))) ≤
            (6 * L * R / (C * Real.exp (Real.sqrt K))) *
              caseI1423RemainderUnit B (D : ℝ) σ ∧
          caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
            (12 * R) * caseI1423RemainderUnit B (D : ℝ) σ := by
  let E : ℝ := Real.exp (Real.sqrt K)
  let A11 : ℝ := 6 * L * R / (C * E)
  let A12 : ℝ := 12 * R
  have hE : 0 < E := Real.exp_pos _
  intro D M hD3 hscalar hM hM2 h2σ
  dsimp only
  let σ := sourceSigma (D : ℝ) d
  let z := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  let E0 := errorEnvelope H M (D : ℝ) d 2
  have hD : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    have he : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact (Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 he
  have hσ0 : 0 < σ := by dsimp [σ]; linarith
  have hlogσ : 0 < Real.log (Real.exp 1 * σ) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hσ0), Real.log_exp]
    have := Real.log_nonneg (by linarith : 1 ≤ σ)
    linarith
  have hE0 : 0 ≤ E0 := by
    dsimp [E0]
    exact errorEnvelope_nonneg H M hD (by norm_num)
      (hH.positive (ErrorSign.ofDepth M) 2 (by norm_num)).le
  have hrev := hratio (ErrorSign.ofDepth M) 2 σ (by norm_num) h2σ
  have hfin := hfinite M hM hM2
  have htransport : finiteSourceLayer 1 2 (M - 1) 1 ≤
      L * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by
    have hTpos := hH.positive (ErrorSign.ofDepth M) 2 (by norm_num)
    have hquot := (div_le_iff₀ hTpos).mp hrev
    have hpert : 2 * H.T (ErrorSign.ofDepth M) 2 ≤ E0 := by
      dsimp [E0, errorEnvelope, Section13HatLayers.kappaHat]
      norm_num [Real.rpow_one]
      have hbase : 1 ≤ 1 + (2 : ℝ) ^ d / Real.log (D : ℝ) := by
        have : 0 ≤ (2 : ℝ) ^ d / Real.log (D : ℝ) :=
          div_nonneg (Real.rpow_nonneg (by norm_num) _) hlog.le
        linarith
      have hp := Real.one_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 2)
      have hsp : 1 * (2 * H.T (ErrorSign.ofDepth M) 2) ≤
          (1 + (2 : ℝ) ^ d / Real.log (D : ℝ)) ^ (2 : ℝ) *
            (2 * H.T (ErrorSign.ofDepth M) 2) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) hTpos.le)
      simpa [errorEnvelope, Section13HatLayers.kappaHat,
        Real.rpow_one, mul_assoc] using hsp
    calc
      finiteSourceLayer 1 2 (M - 1) 1 ≤
          L * H.T (ErrorSign.ofDepth M).opposite 1 := hfin
      _ ≤ L * ((R * (σ * Real.log (Real.exp 1 * σ))) *
          (2 * H.T (ErrorSign.ofDepth M) 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith [hL])
        norm_num at hquot
        have hA : 0 ≤ R * (σ * Real.log (Real.exp 1 * σ)) := by positivity
        calc
          H.T (ErrorSign.ofDepth M).opposite 1 ≤
              R * (σ * Real.log (Real.exp 1 * σ)) * H.T (ErrorSign.ofDepth M) 2 := hquot
          _ ≤ R * (σ * Real.log (Real.exp 1 * σ)) *
              (2 * H.T (ErrorSign.ofDepth M) 2) :=
            mul_le_mul_of_nonneg_left (by linarith [hTpos.le]) hA
      _ ≤ L * ((R * (σ * Real.log (Real.exp 1 * σ))) * E0) := by gcongr
      _ = L * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by ring
  have hq : qD H (ErrorSign.ofDepth M).opposite (D : ℝ) d Δ 2 ≤
      2 * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by
    have hfixed := caseISigma12_qD_le_fixedFactor_mul_errorEnvelope
      hH.toSection13HatContract M (D := (D : ℝ)) (d := d) (Δ := Δ)
        (s := (2 : ℝ)) hD (by norm_num)
    norm_num [caseISigma12QDFixedFactor, proposition131iiiReverseRatio] at hfixed
    norm_num [proposition131iiiReverseRatio] at hrev
    have hratio0 : 0 ≤ H.T (ErrorSign.ofDepth M).opposite 1 /
        H.T (ErrorSign.ofDepth M) 2 :=
      div_nonneg (hH.positive _ _ (by norm_num)).le
        (hH.positive _ _ (by norm_num)).le
    have hpow : (2 : ℝ) ^ Δ ≤ 2 := by
      calc
        (2 : ℝ) ^ Δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hΔ1.le
        _ = 2 := by norm_num
    have hfac : (2 : ℝ) ^ Δ *
        (H.T (ErrorSign.ofDepth M).opposite 1 / H.T (ErrorSign.ofDepth M) 2) ≤
        2 * (R * (σ * Real.log (Real.exp 1 * σ))) :=
      mul_le_mul hpow hrev hratio0 (by positivity)
    calc
      qD H (ErrorSign.ofDepth M).opposite (D : ℝ) d Δ 2 ≤
          (2 : ℝ) ^ Δ *
            (H.T (ErrorSign.ofDepth M).opposite 1 / H.T (ErrorSign.ofDepth M) 2) * E0 := hfixed
      _ ≤ (2 * (R * (σ * Real.log (Real.exp 1 * σ)))) * E0 :=
        mul_le_mul_of_nonneg_right hfac hE0
      _ = 2 * R * (σ * Real.log (Real.exp 1 * σ)) * E0 := by ring

  have hlog1 : 1 ≤ Real.log (D : ℝ) := by
    have he : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast (show 3 ≤ D by omega)
    exact ((Real.lt_log_iff_exp_lt (by positivity : 0 < (D : ℝ))).2 he).le
  have hpowden : (Real.log (D : ℝ)) ^ (1 - Δ) ≤ Real.log (D : ℝ) := by
    calc
      (Real.log (D : ℝ)) ^ (1 - Δ) ≤ (Real.log (D : ℝ)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
      _ = Real.log (D : ℝ) := by norm_num
  have hpowe : (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
      (Real.log (D : ℝ)) ^ (1 - Δ) := by
    calc
      (Real.log (D : ℝ)) ^ (-Δ) * Real.log (D : ℝ) =
          (Real.log (D : ℝ)) ^ (-Δ) * (Real.log (D : ℝ)) ^ (1 : ℝ) := by norm_num
      _ = (Real.log (D : ℝ)) ^ (-Δ + 1) := (Real.rpow_add hlog _ _).symm
      _ = (Real.log (D : ℝ)) ^ (1 - Δ) := by ring_nf
  have hscalarMul : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
      Real.log (Real.log (D : ℝ)) ≤ (Real.log (D : ℝ)) ^ (1 - Δ) :=
    (div_le_one (by positivity)).mp (by simpa [σ] using hscalar)
  constructor
  · rw [log_rpow_one_div_sourceSigma (D := (D : ℝ)) (d := d) (by positivity)]
    have hnorm := evenEndpoint_sigma11_normalization K σ
      (Real.log (Real.exp 1 * σ)) (Real.log (D : ℝ))
      (Real.log (Real.log (D : ℝ))) Δ hlog hll hσ0 hscalarMul hpowe
    have hL0 : 0 ≤ L := by linarith [hL]
    have hR0 : 0 ≤ R := by linarith [hR]
    calc
      suzukiVProduct S z *
          (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
            (Real.log (D : ℝ) / σ)) =
          6 * suzukiVProduct S z * (K ^ 2 * σ / Real.log (D : ℝ)) *
            finiteSourceLayer 1 2 (M - 1) 1 :=
        evenEndpoint_sigma11_front _ _ _ _ _ hlog hσ0
      _ ≤ 6 * suzukiVProduct S z * (K ^ 2 * σ / Real.log (D : ℝ)) *
          (L * R * (σ * Real.log (Real.exp 1 * σ)) * E0) := by
        apply mul_le_mul_of_nonneg_left htransport
        exact mul_nonneg
          (mul_nonneg (by norm_num) (suzukiVProduct_pos S (z : ℝ)).le)
          (div_nonneg (mul_nonneg (sq_nonneg K) hσ0.le) hlog.le)
      _ = 6 * L * R * suzukiVProduct S z * E0 *
          (K ^ 2 * σ ^ 2 * Real.log (Real.exp 1 * σ) / Real.log (D : ℝ)) := by ring
      _ ≤ 6 * L * R * suzukiVProduct S z * E0 *
          ((Real.log (D : ℝ)) ^ (-Δ) /
            (Real.log (Real.log (D : ℝ)) * σ)) := by
        apply mul_le_mul_of_nonneg_left hnorm
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hL0) hR0)
              (suzukiVProduct_pos S (z : ℝ)).le) hE0
      _ = A11 * caseI1423RemainderUnit
          (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
        dsimp [A11, E, E0, caseI1423RemainderUnit, sigma12InheritedBudget]
        exact evenEndpoint_sigma11_budget L R C (Real.exp √K)
          (suzukiVProduct S (z : ℝ))
          (errorEnvelope H M (D : ℝ) d 2) ((Real.log (D : ℝ)) ^ (-Δ))
          (Real.log (Real.log (D : ℝ))) σ hC (Real.exp_pos _) hll hσ0
  · unfold caseI1423Sigma12Endpoint caseI1423RemainderUnit sigma12InheritedBudget
    rw [log_rpow_one_div_sourceSigma (D := (D : ℝ)) (d := d) (by positivity)]
    dsimp [σ, z, A12, E, E0] at hq ⊢
    have hfront := mul_le_mul_of_nonneg_left hq
      (mul_nonneg (mul_nonneg (mul_nonneg hC.le hE.le)
        (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg hlog.le (-Δ)))
    have hscalar12 : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
        Real.log (Real.log (D : ℝ)) / Real.log (D : ℝ) ≤ 1 := by
      calc
        _ ≤ K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
            Real.log (Real.log (D : ℝ)) /
              (Real.log (D : ℝ)) ^ (1 - Δ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpowden
        _ ≤ 1 := by simpa [σ] using hscalar
    have hscalar12Mul : K ^ 2 * σ ^ 3 * Real.log (Real.exp 1 * σ) *
        Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) :=
      (div_le_one hlog).mp hscalar12
    field_simp [ne_of_gt hlog, ne_of_gt hll, ne_of_gt hσ0] at hfront ⊢
    exact evenEndpoint_sigma12_algebra
      (qD H (ErrorSign.ofDepth M).opposite (D : ℝ) d Δ 2)
      (suzukiVProduct S (z : ℝ)) K R σ (Real.log (Real.exp 1 * σ)) E0
      (Real.log (Real.log (D : ℝ))) (Real.log (D : ℝ))
      (by linarith [hR]) hσ0 hE0 (suzukiVProduct_pos S (z : ℝ)).le hll.le
      (by simpa [mul_comm] using hfront) hscalar12Mul

/-- Closed-endpoint analogue of `caseI1423EndpointSourceBoundsFinal`. -/
theorem caseI1423EndpointSourceBounds_evenEndpoint_of_sourceScalar
    (S : BoundingSieve) (H : Section13HatLayers) (C K d Δ : ℝ)
    (hH : Section13HatSourceContract H) (hC : 0 < C)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    CaseI1423EvenEndpointSourceBoundsSourceScalar S H C K d Δ := by
  obtain ⟨L, hL, hfinite⟩ :=
    lemma132_finiteSourceLayer_evenEndpoint_uniform_sourceLargeConsumer hH
  obtain ⟨R, hR, hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  refine ⟨6 * L * R / (C * Real.exp (Real.sqrt K)), 12 * R,
    by positivity, by positivity, ?_⟩
  exact caseI1423EndpointSourceBounds_evenEndpoint_explicit
    S H C K d Δ L R hH hC hΔ0 hΔ1 hd hL hfinite hR hratio

/-- Even `s=2` Case-I successor with the same error constant and moving IH. -/
theorem lemma14_4_caseI_evenEndpoint_sameC_successor_of_sourceScalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {Dmin : ℕ} {C C145 K d Δ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hC : 0 < C) (hC145 : 0 < C145)
    (hDmin : 2 ≤ Dmin) :
    ∀ᶠ D : ℕ in atTop, ∀ M : ℕ, Even M → 2 ≤ M →
      (2 : ℝ) ≤ sourceSigma (D : ℝ) d →
      K ^ 2 * sourceSigma (D : ℝ) d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma (D : ℝ) d) *
          Real.log (Real.log (D : ℝ)) /
          (Real.log (D : ℝ)) ^ (1 - Δ) ≤ 1 →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) Dmin →
      suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
        suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
          finiteSourceLayer 1 2 M 2 +
        sigma12InheritedBudget S H M D
          ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  obtain ⟨D0, _, hzero⟩ := suzukiSigmaZero_sourceSigma_eventually
    S H hΔ0 hΔ1 hd (lt_of_lt_of_le (by norm_num) hK) hC145 hlocal hH
  obtain ⟨A0, hA0, hzeroSource⟩ :=
    caseI1423_sigmaZero_realEndpoint_sourceBound_uniform
      S H C C145 K d Δ hH hd1 hΔ0 hΔ1 hC hC145.le
  obtain ⟨A11, A12, hA11, hA12, hendpoint⟩ :=
    caseI1423EndpointSourceBounds_evenEndpoint_of_sourceScalar
      S H C K d Δ hH hC hΔ0 hΔ1 hd
  obtain ⟨D12, _hD12, h12⟩ :=
    eventually_sigmaTwelve_internal_contraction_sameC_uniform
    (S := S) (H := H) (C := C) (K := K) (d := d) (Δ := Δ)
      hH hd1 hΔ0 hΔ1 hK hlocal hC.le
  have hcoefN := tendsto_natCast_atTop_atTop.eventually
    (eventually_caseISourceOrderCoefficient_le_sameC_gap
      (A := A0 + A11 + A12) (by positivity) hΔ0 hΔ1 hd)
  have hD0N : ∀ᶠ D : ℕ in atTop, D0 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D0)
  obtain ⟨Dg, _, hg⟩ := exists_caseI_preThreshold_geometry_packet d hd1
  have hDgN : ∀ᶠ D : ℕ in atTop, Dg ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Dg)
  have hD12N : ∀ᶠ D : ℕ in atTop, D12 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D12)
  have hrecursiveEvent := eventually_recursiveCoordinate_le_quotient_sourceSigma S hd1
  have herrorUniform := eventually_caseI_errorEnvelope_transport_uniform
    S H hH hd1 hΔ0 hΔ1
  have hDsq : ∀ᶠ D : ℕ in atTop, Dmin ^ 2 ≤ D := eventually_ge_atTop _
  filter_upwards [hD12N, hzeroSource, hcoefN, hD0N, hDgN,
    hrecursiveEvent, herrorUniform, hDsq, eventually_ge_atTop (3 : ℕ)]
    with D h12D hzeroSrcD hcoefD hlarge0 hDg hrecursiveD herrorD hDsqD hD3
  intro M hM hM2 h2σ hscalar hglobal
  have g := hg D M hDg 2 (by norm_num) h2σ
  have hDpos : 0 < D := lt_of_lt_of_le (by omega : 0 < 4) g.hD4
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ := rfl
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp; exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2 →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D Dmin σ 2 := by
    intro p hp
    exact evenEndpoint_carrier_scale S hDmin hDsqD p (toFull p hp)
  have hrecursiveSigma : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp; exact hrecursiveD 2 (by norm_num) p (toFull p hp)
  have hinheritedFull : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    apply lemma144_caseI_even_endpoint_inherited_domain S hM hM2 g.hD4 hz p
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hp).1,
      (nat_lt_natCeil_iff_lt_real (natCast_rpow_one_div_pos (hDpos) (2 : ℝ)) hz).2
        (Finset.mem_filter.mp hp).2.2⟩
  have herror : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp
    exact herrorD M 2 (by norm_num) hinheritedFull (hrecursiveD 2 (by norm_num))
      p (toFull p hp)
  have hpoint := evenEndpoint_pointwiseContract_of_movingIH_sourceLargeConsumer
    S H C K d Δ M D Dmin hDmin hM hM2 g.hD4 hscale hrecursiveSigma herror hC.le hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ 2
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprime p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have hDreal : 1 < (D : ℝ) := by
    exact_mod_cast (show 1 < D from lt_of_lt_of_le (by omega : 1 < 4) g.hD4)
  have hzσ : (D : ℝ) ^ (1 / σ) ≤ (z : ℝ) := g.hpowerOrder.trans (Nat.le_ceil _)
  have hOddσ : Odd M → ⌈(D : ℝ) ^ (1 / σ)⌉₊ ^ 3 ≤ D := by
    intro hOdd
    exact (Nat.not_even_iff_odd.mpr hOdd hM).elim
  have hzeroDirect : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      caseISigmaZeroDirectRemainder S H M D C145 K d Δ := by
    simpa [σ, caseISigmaZeroDirectRemainder] using
      hzero D M z hlarge0 hM2 hzσ hOddσ
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / (2 : ℝ))) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) := by
    simpa [σ] using suzuki_equation14_9_strict (D := D) (z := z) S hM2
      (fun hOdd => (Nat.not_even_iff_odd.mpr hOdd hM).elim) g.hpowerOrder
  have h11 := caseI_evenEndpointSigma11Edge S hM hM2 h2σ hDreal
    g.hpowerS g.hpowerSigma g.hpowerOrder hK hlocal
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    exact ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      (Nat.mul_le_mul_right p hDmin).trans (evenEndpoint_carrier_scale S hDmin hDsqD p hpc)⟩
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (M - 1)) (inheritedCoordinate D p) := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    have hcoord := hinheritedFull p hpc
    have hpred : (M - 1) % 2 = 1 := by
      have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
      omega
    have hcoord0 : 0 < inheritedCoordinate D p := by
      simp only [KappaOneModel.parityDomain, hpred, if_pos, Set.mem_Ioi] at hcoord
      norm_num at hcoord
      linarith
    exact (hH.positive _ _ hcoord0).le
  have hEvenLower : 2 + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    have hnotOdd : ¬ Odd M := fun ho => (Nat.not_even_iff_odd.mpr ho) hM
    simp [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon]
  obtain ⟨q12, hq12, _h12raw, h12q⟩ := h12 D h12D M 2 z hM2 (by norm_num)
    hEvenLower
    g.hsigma h2σ hDreal g.hpowerS g.hpowerSigma g.hpowerOrder hz
    (by rw [hH.betaHat_eq]; exact hEvenLower)
    hceil hT
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ 2 ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ 2 +
          sigma12EndpointRemainder S H M D z C K d Δ 2 σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ 2
      (by dsimp [z]; exact Nat.le_ceil _)]
    exact h12q
  have h12qSupported' :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ 2 ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ 2 +
          caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ := by
    simpa [sigma12EndpointRemainder, caseI1423Sigma12Endpoint] using h12qSupported
  have hzeroSrc := hzeroSrcD M 2 hEvenLower h2σ
  have hend := hendpoint D M hD3 hscalar hM hM2 h2σ
  obtain ⟨qgap, hqgap, hcoef⟩ := hcoefD
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ 2 := by
    unfold sigma12InheritedBudget
    have henv := errorEnvelope_nonneg (d := d) H M hDreal
      (by norm_num : (0 : ℝ) ≤ 2)
      (hH.positive (ErrorSign.ofDepth M) 2 (by norm_num)).le
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC.le (Real.exp_nonneg _))
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _)) henv
  have hunit : (A0 + A11 + A12) *
        caseI1423RemainderUnit (sigma12InheritedBudget S H M D z C K d Δ 2)
          (D : ℝ) σ =
      caseISourceOrderCoefficient (A0 + A11 + A12) (D : ℝ) d *
        sigma12InheritedBudget S H M D z C K d Δ 2 := by
    simp [caseI1423RemainderUnit, caseISourceOrderCoefficient, σ]; ring
  have hside : caseISigmaZeroDirectRemainder S H M D C145 K d Δ +
        suzukiVProduct S z * (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log ((D : ℝ) ^ (1 / σ))) +
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
      (1 - q12.ρ) * sigma12InheritedBudget S H M D z C K d Δ 2 := by
    have hsrc := add_le_add (add_le_add hzeroSrc hend.1) hend.2
    calc
      _ ≤ (A0 + A11 + A12) * caseI1423RemainderUnit
          (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by linarith
      _ = _ := hunit
      _ ≤ (1 - qgap.ρ) * sigma12InheritedBudget S H M D z C K d Δ 2 :=
        mul_le_mul_of_nonneg_right hcoef hbudget
      _ = _ := by rw [hqrho]
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S g.hD4 (by norm_num : (2 : ℝ) ≤ 2) hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) = 0 := by
    simpa [lemma144_realTau_eq_s_of_caseI g.hD4 (by norm_num : (2 : ℝ) ≤ 2)] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / (2 : ℝ))) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ 2 +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ 2 := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ 2 ≤ _
    exact h10
  dsimp [CaseIEvenEndpointSigma11Edge] at h11
  rw [h149, h2]
  linarith [hzeroDirect, hmiddle, h11, h12qSupported', hside]

/-- Source-large-log even endpoint. `C1min` is selected before all later
`C1,C,C145,K,Dmin,D,M`; the scalar endpoint input is discharged pointwise from
`C1*K^Theta < log D`. -/
theorem exists_lemma14_4_caseI_evenEndpoint_sameC_sourceLargeLog
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H) (hd1 : 1 < d)
    (hΔ0 : 0 < Δ) (hΘ : 0 < Θ)
    (hmargin : Δ + 2 / Θ < 1)
    (hd : 7 / (1 - (Δ + 2 / Θ)) < d) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 C C145 K : ℝ) (Dmin : ℕ),
        C1min ≤ C1 → 2 ≤ K → HasDimensionOneLocalProductBound S K →
        0 < C → 0 < C145 → 2 ≤ Dmin →
        ∀ᶠ D : ℕ in atTop, ∀ M : ℕ, Even M → 2 ≤ M →
          (2 : ℝ) ≤ sourceSigma (D : ℝ) d →
          C1 * K ^ Θ < Real.log (D : ℝ) →
          Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) Dmin →
          suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
            suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
              finiteSourceLayer 1 2 M 2 +
            sigma12InheritedBudget S H M D
              ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  obtain ⟨C1min, hC1min, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform hΔ0 hΘ hmargin hd
  refine ⟨C1min, hC1min, ?_⟩
  intro C1 C C145 K Dmin hC1 hK hlocal hC hC145 hDmin
  have hη0 : 0 < 2 / Θ := by positivity
  have hΔ1 : Δ < 1 := by linarith [hmargin, hη0]
  have hdWeak : 7 / (1 - Δ) < d := by
    have hden : 0 < 1 - (Δ + 2 / Θ) := sub_pos.mpr hmargin
    have hdenWeak : 0 < 1 - Δ := by linarith [hη0]
    have hfrac : 7 / (1 - Δ) ≤ 7 / (1 - (Δ + 2 / Θ)) := by
      apply (div_le_div_iff₀ hdenWeak hden).2
      nlinarith [hη0]
    exact hfrac.trans_lt hd
  have hsucc := lemma14_4_caseI_evenEndpoint_sameC_successor_of_sourceScalar
    S H hH hd1 hΔ0 hΔ1 hdWeak hK hlocal hC hC145 hDmin
  filter_upwards [hsucc, eventually_ge_atTop (2 : ℕ)] with D hsuccD hD2
  intro M hM hM2 h2σ hlarge hglobal
  exact hsuccD M hM hM2 h2σ
    (hscalar C1 K (D : ℝ) hC1 hK (by exact_mod_cast hD2) hlarge) hglobal


end MathlibNt.SieveTheory
