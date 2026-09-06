import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIRawRoundedTransportRefactor
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIErrorTransportUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIOddFinalProducer
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket

import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim1413Internal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3000000

/-- The source parity indices coincide with the actual recurrence carrier. -/
theorem sourceParityIndices_eq_actualParityCarrier (n : ℕ) :
    sourceParityIndices n = suzukiActualParityCarrier n := by
  ext m
  simp [sourceParityIndices, suzukiActualParityCarrier]
  omega

private theorem caseII_raw_cubic_scale
    (S : BoundingSieve) {D Dmin : ℕ} {d : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) :
    CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
      D Dmin (sourceSigma (D : ℝ) d) 3 := by
  exact MathlibNt.SieveTheory.caseII_cubic_carrier_quotient_scale
    (D := D) (Dmin := Dmin) (d := d) S hDmin hD

/-- A prime below the cubic cutoff has inherited logarithmic coordinate above two. -/
theorem caseII_raw_inherited_gt_two
    {D p : ℕ} (hp : 2 ≤ p) (hD : 1 < D)
    (hupper : (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ))) :
    2 < inheritedCoordinate D p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hDR : (0 : ℝ) < (D : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hloglt := Real.strictMonoOn_log (show (p : ℝ) ∈ Set.Ioi 0 by exact hpR)
    (show (D : ℝ) ^ (1 / (3 : ℝ)) ∈ Set.Ioi 0 by
      exact Real.rpow_pos_of_pos hDR _)
    hupper
  rw [Real.log_rpow hDR] at hloglt
  unfold inheritedCoordinate
  rw [lt_sub_iff_add_lt, lt_div_iff₀ hlogp]
  norm_num [one_div] at hloglt ⊢
  nlinarith

/-- The genuine large-parameter raw rounded Case-II producer.  Its cutoff is
chosen before `D`, `N`, and `s`; the only recursive input left at a particular
`N` is the global depth-`N-1` induction hypothesis. -/
theorem eventually_lemma144_caseII_odd_rawRoundedFinal
    (S : BoundingSieve) (H : Section13HatLayers)
    {Dmin : ℕ} {d Δ C K : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hC3 : 3 ≤ C) (hK : 2 ≤ K)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hDmin : 2 ≤ Dmin) :
    ∀ᶠ D : ℕ in atTop, ∀ (N : ℕ) (s : ℝ),
      Odd N → 3 ≤ N → 1 < s → s ≤ 3 →
      GlobalDepthLemma144InductionHypothesis
        (suzukiActualT S) (fun p => suzukiVProduct S p)
        (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
        2 C K Δ (N - 1) Dmin →
      let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
        caseIIOddClaim145Endpoint S d N D + suzukiVProduct S (z : ℝ) *
          (finiteSourceLayer 1 2 N s +
            (C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) *
            caseIIConcreteRoundedRelativeBracket N (D : ℝ) d Δ
              (sourceSigma (D : ℝ) d) C K) := by
  obtain ⟨Dg, _hDg, hg⟩ :=
    exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  have hgeom : ∀ᶠ D : ℕ in atTop, Dg ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Dg)
  have herr := eventually_caseII_errorEnvelope_transport_uniform S H hH hd1
  obtain ⟨D146, _hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  have hclaim : ∀ᶠ D : ℕ in atTop, D146 ≤ (D : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop D146)
  filter_upwards [hgeom, herr, hclaim, eventually_ge_atTop (Dmin ^ 2)]
    with D hDg herrorD hD146 hDsq
  intro N s hN hN3 hs1 hs3 hglobal
  have hD4 : 4 ≤ D := by
    have : 4 ≤ Dmin ^ 2 := by nlinarith
    exact this.trans hDsq
  have hDnat1 : 1 < D := by omega
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hDnat1
  let y : ℕ := ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let σ : ℝ := sourceSigma (D : ℝ) d
  have g := hg S D hDg s hs1 hs3
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S y) D Dmin σ 3 := by
    simpa [y, σ] using caseII_raw_cubic_scale (d := d) S hDmin hDsq
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp _hpl hpu
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have hrootle : (D : ℝ) ^ (1 / (3 : ℝ)) ≤ (y : ℝ) := by
      simpa [y] using Nat.le_ceil ((D : ℝ) ^ (1 / (3 : ℝ)))
    have hpD : (2 : ℝ) * p ≤ (D : ℝ) := by
      have hpyle : (p : ℝ) ≤ (y : ℝ) := hpu.le.trans hrootle
      linarith [g.hyDhalf]
    exact ⟨hp2, by exact_mod_cast hpD⟩
  have hdomains : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) ∧
      recursiveCoordinate D p ∈ KappaOneModel.parityDomain 2 (N - 1) := by
    intro p hpCarrier
    have hp' := hpCarrier
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    have hpFull : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp'.1).1
    obtain ⟨hp2, h2p⟩ := hceil p hpFull hp'.2.1 (by simpa [y] using hp'.2.2)
    have hinherited2 : 2 ≤ inheritedCoordinate D p :=
      (caseII_raw_inherited_gt_two hp2 (by omega) (by simpa [y] using hp'.2.2)).le
    have hrec2 : 2 ≤ recursiveCoordinate D p :=
      hinherited2.trans (coordinate_bounds hp2 h2p).1
    have hNm : (N - 1) % 2 = 0 := by
      have hmod : N % 2 = 1 := Nat.odd_iff.mp hN
      omega
    constructor <;> simp [KappaOneModel.parityDomain, *]
  have herror : CaseIIErrorEnvelopeTransport S H N D d :=
    herrorD N s hN hs1 hs3 (by simpa [y, σ] using hdomains)
  have hsource : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      finiteSourceLayer 1 2 (N - 1) (recursiveCoordinate D p) ≤
        finiteSourceLayer 1 2 (N - 1) (inheritedCoordinate D p) := by
    intro p hpCarrier
    have hp' := hpCarrier
    simp only [sigmaOneCarrier, Finset.mem_filter] at hp'
    have hpFull : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp hp'.1).1
    obtain ⟨hp2, h2p⟩ := hceil p hpFull hp'.2.1 (by simpa [y] using hp'.2.2)
    exact finiteSourceLayer_recursive_le_inherited (by norm_num) (N - 1) D p
      hp2 h2p (hdomains p hpCarrier).1 (hdomains p hpCarrier).2
  have hIH : NaturalCeilPointwiseInductionContract
      (suzukiSupportedBelow S y)
      (fun n D' p => ∑ m ∈ sourceParityIndices n, suzukiSourceV S m D' p)
      (fun p => suzukiVProduct S p)
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      2 C K Δ N D σ 3 := by
    intro p hpCarrier
    have hpSupport : p ∈ suzukiSupportedBelow S y :=
      (Finset.mem_filter.mp hpCarrier).1
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpSupport).1
    have hqmin := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hpCarrier)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqmin
    change (∑ m ∈ sourceParityIndices (N - 1),
      suzukiSourceV S m (D ⌈/⌉ p) p) ≤ _
    rw [sourceParityIndices_eq_actualParityCarrier,
      ← suzukiActualT_eq_parity_sum]
    exact hglobal (D ⌈/⌉ p) p hqmin hq2 hpPrime.two_le
      (recursiveCoordinate D p) (hdomains p hpCarrier).2
      (recursiveCoordinate_power_identity hpPrime.two_le hq2)
  have hEndpoint : Claim14_5Regime 2 (D : ℝ) σ C K σ σ →
      (∑ p ∈ suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / σ)⌉₊,
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) ≤
        caseIIOddClaim145Endpoint S d N D := by
    intro _
    have hwle : ⌈(D : ℝ) ^ (1 / σ)⌉₊ ≤ y := by
      exact Nat.ceil_mono (by simpa [σ] using g.hwy)
    have hrec := suzukiActualT_caseI_recurrence_strict
      (S := S) (N := N) (D := D)
      (z := ⌈(D : ℝ) ^ (1 / σ)⌉₊) (by omega)
      (by
        intro _ p hp
        have hpw : (p : ℝ) < (D : ℝ) ^ (1 / σ) := by
          simpa [Nat.lt_ceil] using hp
        have hpcubeRoot : (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) :=
          hpw.trans_le (by simpa [σ] using g.hwy)
        have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
        have hiff := Real.lt_rpow_inv_iff_of_pos
          (x := (p : ℝ)) (y := (D : ℝ)) (z := (3 : ℝ))
          (by positivity) hDR.le (by norm_num)
        have hcubeR : (p : ℝ) ^ (3 : ℕ) < (D : ℝ) := by
          norm_num [one_div] at hiff hpcubeRoot ⊢
          exact hiff.mp hpcubeRoot
        exact_mod_cast hcubeR)
    rw [caseIIOddClaim145Endpoint]
    simp_rw [sourceParityIndices_eq_actualParityCarrier,
      ← suzukiActualT_eq_parity_sum]
    simpa [σ] using le_of_eq hrec.symm
  have hnu : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ S.nu p := by
    intro p hp
    have hpf : p ∈ S.prodPrimes.primeFactors :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
    exact (S.nu_pos_of_prime p (Nat.mem_primeFactors.mp hpf).1
      (Nat.mem_primeFactors.mp hpf).2.1).le
  have hlog : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S y) D σ 3,
      0 ≤ Real.log ((D ⌈/⌉ p : ℕ) : ℝ) := by
    intro p hp
    have hps : p ∈ suzukiSupportedBelow S y := (Finset.mem_filter.mp hp).1
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hps).1
    have hqmin := ceilDiv_ge_threshold_of_scale hpPrime.pos (hscale p hp)
    have hq2 : 2 ≤ D ⌈/⌉ p := hDmin.trans hqmin
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ D ⌈/⌉ p by omega))
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (N - 1)) (inheritedCoordinate D p) := by
    intro p hp _hpl hpu
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    exact (hH.positive _ _ (by
      have := caseII_raw_inherited_gt_two hp2 hDnat1 hpu
      linarith)).le
  have h1413 : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (3 : ℝ)) →
      Claim14_13PointwisePremise H N (D : ℝ) d Δ
        (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)) := by
    intro p hp hpl hpu
    obtain ⟨hp2, h2p⟩ := hceil p hp (by simpa [σ] using hpl) hpu
    exact claim14_13_pointwise_carrier H (by omega) hp2 h2p hd1 hΔ0
      (by simpa [inheritedCoordinate] using hT p hp hpl hpu)
  obtain ⟨_hi, hii, hiiiAll⟩ := h146 (D : ℝ) hD146
  have hsign3 : 2 + (ErrorSign.ofDepth N).epsilon ≤ (3 : ℝ) := by
    rw [ErrorSign.ofDepth_of_odd hN]
    norm_num [ErrorSign.epsilon]
  have hiii := (hiiiAll (ErrorSign.ofDepth N) 3 hsign3 g.h3σ).le
  have hcut : 0 ≤ (1 - 1 / σ) ^ (1 - Δ) := by
    apply Real.rpow_nonneg
    have hσ0 : 0 < σ := by dsimp [σ]; linarith [g.h3σ]
    have : 1 / σ ≤ 1 := (div_le_one hσ0).2 (by linarith [g.h3σ])
    linarith
  have hLambda := lambda_three_le_perturb_three_mul_lambda_caseII
    hH.toSection13HatContract hDreal1 (by linarith : 0 ≤ d)
    (zero_lt_one.trans hs1) hs3
  have hE := one_third_le_errorEnvelope_caseII
    (d := d) hH.toSection13HatContract hN hDreal1 hs1 hs3
  have hP : 1 ≤ C * Real.exp (Real.sqrt K) := by
    have hexp : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg K)
    nlinarith [mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ C)]
  have hPE : 1 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s := by
    have hexp : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg K)
    have hP3 : 3 ≤ C * Real.exp (Real.sqrt K) := by
      calc 3 ≤ C := hC3
           _ = C * 1 := by ring
           _ ≤ C * Real.exp (Real.sqrt K) :=
             mul_le_mul_of_nonneg_left hexp (by linarith)
    nlinarith [mul_le_mul hP3 hE (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by positivity : 0 ≤ C * Real.exp (Real.sqrt K))]
  dsimp only [z]
  exact caseII_total_le_doubleRounded_direct_concrete_relative_natCeil_of_errorTransport
    (S := S) (H := H) (N := N) (D := D) (y := y) (z := z)
    (σ := σ) (C := C) (C1 := C) (K := K) (ΘK := σ)
    (Δ := Δ) (d := d) (B0 := caseIIOddClaim145Endpoint S d N D) (s := s)
    hH.toSection13HatContract hN (by omega) g.hycube g.hyceil g.hyDhalf
    g.h3σ g.hD g.hDlarge g.hwy g.hy2 g.hyr2 g.hw2 hEndpoint hnu
    (by linarith) hlog hdomains herror hIH
    (by
      rw [hH.toSection13HatContract.betaHat_eq, ErrorSign.ofDepth_of_odd hN]
      norm_num [ErrorSign.epsilon])
    hK hlocal (by simpa [σ] using hii) hΔ0 hΔ1
    (by simpa [σ] using hceil) hT h1413 hs1 hs3 g.hyrzr g.hyz
    g.hyLower g.hyUpper g.hzceil g.hzr2 g.h3dlog hE hcut hiii
    (by rw [ErrorSign.ofDepth_of_odd hN]; exact hLambda) hP hPE


end MathlibNt.SieveTheory
