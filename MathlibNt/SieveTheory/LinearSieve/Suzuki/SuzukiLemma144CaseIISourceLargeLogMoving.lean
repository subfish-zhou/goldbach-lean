import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIExactRatioDirectAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIMovingFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIISourceLargeLogUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseBUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 5000000

private theorem caseII_raw_cubic_scale
    (S : BoundingSieve) {D Dmin : ℕ} {d : ℝ}
    (hDmin : 2 ≤ Dmin) (hD : Dmin ^ 2 ≤ D) :
    CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S ⌈(D : ℝ) ^ (1 / (3 : ℝ))⌉₊)
      D Dmin (sourceSigma (D : ℝ) d) 3 := by
  exact MathlibNt.SieveTheory.caseII_cubic_carrier_quotient_scale
    (D := D) (Dmin := Dmin) (d := d) S hDmin hD

/-- The same-constant Case-II bound implies the literal actual recurrence bound. -/
theorem caseII_sameCAt_to_literal_moving
    (S : BoundingSieve) (H : Section13HatLayers)
    {M D : ℕ} {d Δ C K s : ℝ}
    (h : Lemma144CaseIISameCAt S H M D d Δ C K s) :
    suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 M s +
          C * Real.exp (Real.sqrt K) * errorEnvelope H M (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
  dsimp [Lemma144CaseIISameCAt] at h
  rw [suzukiActualT_eq_parity_sum, ← sourceParityIndices_eq_actualParityCarrier]
  exact h

/-- Source-large Case-II closure with the cutoff chosen before the varying
bounding sieve, `C1`, the same error constant `C`, `K`, the odd depth, `D`, and
`s`.  The proof uses the actual moving predecessor IH and the exact-ratio
rounded transport packet; no sieve- or fixed-`K` eventual cutoff occurs. -/
theorem exists_lemma144_caseII_odd_sameC_sourceLargeLog_uniform_moving_uniform_in_S
    (H : Section13HatLayers)
    {Dmin : ℕ} {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hDmin : 2 ≤ Dmin) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (N D : ℕ) (s : ℝ),
        C1min ≤ C1 → 3 ≤ C → 2 ≤ K → 2 ≤ D →
        HasDimensionOneLocalProductBound S K →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Odd N → 3 ≤ N → 1 < s → s ≤ 3 →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (N - 1) Dmin →
        Lemma144CaseIISameCAt S H N D d Δ C K s := by
  have hbeta : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
  have hd7 : 7 < d := by
    have hfrac : 7 ≤ 7 / (1 - Δ) := by
      rw [le_div_iff₀ hbeta]
      nlinarith [hsrc.hDelta_pos]
    exact hfrac.trans_lt hsrc.h14_1
  have hd1 : 1 < d := by linarith
  obtain ⟨Dg, _hDg, hg⟩ :=
    exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  obtain ⟨Derr, herrorAt⟩ := eventually_atTop.1
    (eventually_caseII_errorEnvelope_transport_uniform_in_S H hH hd1)
  obtain ⟨Dcoord, hcoordinateAt⟩ := eventually_atTop.1
    (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1)
  obtain ⟨D146, _hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨Cgap, hCgap1, hgap⟩ :=
    exists_caseIIConcreteRoundedRelativeBracketSourceLarge_gap_uniform hH hsrc
  obtain ⟨Ccase, CB, hCcase0, hCB0, hCaseBAll⟩ :=
    claim145_caseB_uniform_in_S H hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1
      hsrc.one_le_theta hH
  obtain ⟨Dconst, _hDconst, hconst3⟩ :=
    exists_claim145_gap_constant_threshold (C := (3 : ℝ)) (C145 := CB)
      (by norm_num) hsrc.hDelta_lt
  let A : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let Dlarge : ℝ := Real.exp (max 1 (3 * A))
  let C1min : ℝ :=
    3 + max 0 Cgap + max 0 Ccase + max 0 Dg +
      (Derr : ℝ) + (Dcoord : ℝ) + max 0 D146 + max 0 Dconst +
      max 0 Dlarge + (Dmin ^ 2 : ℝ)
  have hmGap : 0 ≤ max (0 : ℝ) Cgap := le_max_left _ _
  have hmCase : 0 ≤ max (0 : ℝ) Ccase := le_max_left _ _
  have hmDg : 0 ≤ max (0 : ℝ) Dg := le_max_left _ _
  have hm146 : 0 ≤ max (0 : ℝ) D146 := le_max_left _ _
  have hmConst : 0 ≤ max (0 : ℝ) Dconst := le_max_left _ _
  have hmLarge : 0 ≤ max (0 : ℝ) Dlarge := le_max_left _ _
  have hCmin1 : 1 ≤ C1min := by
    dsimp [C1min]
    nlinarith [hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
  refine ⟨C1min, hCmin1, ?_⟩
  intro S C1 C K N D s hCmin hC3 hK hD2 hlocal hlarge hN hN3 hs1 hs3 hglobal
  have hCaseB := hCaseBAll S
  have hC10 : 0 ≤ C1 := hCmin1.trans hCmin |>.trans' zero_le_one
  have hK1 : 1 ≤ K := by linarith
  have hKpow : 1 ≤ K ^ Θ := Real.one_le_rpow hK1 hsrc.hTheta_pos.le
  have hC1log : C1 < Real.log (D : ℝ) := by
    calc
      C1 = C1 * 1 := by ring
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left hKpow hC10
      _ < Real.log (D : ℝ) := hlarge
  have hCminlog : C1min < Real.log (D : ℝ) := hCmin.trans_lt hC1log
  have hDnat1 : 1 < D := by omega
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hDnat1
  have hD0 : (0 : ℝ) < (D : ℝ) := zero_lt_one.trans hDreal1
  have hlogDlt : Real.log (D : ℝ) < (D : ℝ) := by
    exact (Real.log_le_sub_one_of_pos hD0).trans_lt
      (sub_lt_self _ zero_lt_one)
  have hCminD : C1min < (D : ℝ) := hCminlog.trans hlogDlt
  have hDg : Dg ≤ (D : ℝ) := by
    have hle : Dg ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) Dg
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hDerrR : (Derr : ℝ) ≤ (D : ℝ) := by
    have hle : (Derr : ℝ) ≤ C1min := by
      dsimp [C1min]
      nlinarith [hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hDcoordR : (Dcoord : ℝ) ≤ (D : ℝ) := by
    have hle : (Dcoord : ℝ) ≤ C1min := by
      dsimp [C1min]
      nlinarith [hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hD146 : D146 ≤ (D : ℝ) := by
    have hle : D146 ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) D146
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hDconst : Dconst ≤ (D : ℝ) := by
    have hle : Dconst ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) Dconst
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hDlarge : Dlarge ≤ (D : ℝ) := by
    have hle : Dlarge ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) Dlarge
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCminD.le
  have hDsqR : (Dmin ^ 2 : ℝ) ≤ (D : ℝ) := by
    have hle : (Dmin ^ 2 : ℝ) ≤ C1min := by
      dsimp [C1min]
      exact le_add_of_nonneg_left (by positivity)
    exact hle.trans hCminD.le
  have hDsq : Dmin ^ 2 ≤ D := by exact_mod_cast hDsqR
  have herrorD := herrorAt D (by exact_mod_cast hDerrR) S
  have hcoordinateD := hcoordinateAt D (by exact_mod_cast hDcoordR) S
  have hCgap : Cgap ≤ C1 := by
    have hle : Cgap ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) Cgap
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCmin
  have hCcase : Ccase ≤ C1 := by
    have hle : Ccase ≤ C1min := by
      dsimp [C1min]
      have hm := le_max_right (0 : ℝ) Ccase
      nlinarith [hm, hmGap, hmCase, hmDg, hm146, hmConst, hmLarge]
    exact hle.trans hCmin
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
    have hpCarrierFull : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 3 := by
      exact Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp hpSupport).1, (Finset.mem_filter.mp hpCarrier).2⟩
    exact hglobal (D ⌈/⌉ p) p hqmin hq2 hpPrime.two_le
      (recursiveCoordinate D p) (hdomains p hpCarrier).2
      (by simpa [σ] using hcoordinateD 3 (by norm_num) p hpCarrierFull)
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
    exact claim14_13_pointwise_carrier H (by omega) hp2 h2p hd1 hsrc.hDelta_pos
      (by simpa [inheritedCoordinate] using hT p hp hpl hpu)
  obtain ⟨hi, hii, hiiiAll⟩ := h146 (D : ℝ) hD146
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
  have hP : 3 ≤ C * Real.exp (Real.sqrt K) := by
    have hexp : 1 ≤ Real.exp (Real.sqrt K) := Real.one_le_exp (Real.sqrt_nonneg K)
    calc
      3 ≤ C := hC3
      _ = C * 1 := by ring
      _ ≤ C * Real.exp (Real.sqrt K) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
  have hPE : 1 ≤ C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s := by
    nlinarith [mul_le_mul hP hE (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by positivity : 0 ≤ C * Real.exp (Real.sqrt K))]


  have hrelative :
      (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) ≤
        caseIIOddClaim145Endpoint S d N D + suzukiVProduct S (z : ℝ) *
          (finiteSourceLayer 1 2 N s +
            (C * Real.exp (Real.sqrt K)) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ) *
              caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ) d Δ
                (sourceSigma (D : ℝ) d) K) := by
    exact caseII_total_le_doubleRounded_direct_sourceLarge_relative_natCeil_of_errorTransport
      (S := S) (H := H) (N := N) (D := D) (y := y) (z := z)
      (σ := σ) (C := C) (C1 := C) (K := K) (ΘK := σ)
      (Δ := Δ) (d := d) (B0 := caseIIOddClaim145Endpoint S d N D) (s := s)
      hH.toSection13HatContract hN (by omega) g.hycube g.hyceil g.hyDhalf
      g.h3σ g.hD g.hDlarge g.hwy g.hy2 g.hyr2 g.hw2 hEndpoint hnu
      (by linarith) hlog hdomains herror hIH
      (by
        rw [hH.toSection13HatContract.betaHat_eq, ErrorSign.ofDepth_of_odd hN]
        norm_num [ErrorSign.epsilon])
      hK hlocal (by simpa [σ] using hii) hsrc.hDelta_pos hsrc.hDelta_lt
      (by simpa [σ] using hceil) hT h1413 hs1 hs3 g.hyrzr g.hyz
      g.hyLower g.hyUpper g.hzceil g.hzr2 g.h3dlog hE hcut hiii
      (by rw [ErrorSign.ofDepth_of_odd hN]; exact hLambda) hP hPE
  have hB := hCaseB C1 K N D (sourceSigma (D : ℝ) d)
    hCcase hK hlocal hD2 (by linarith [g.h3σ]) hlarge le_rfl
  have hendpointClaim : caseIIOddClaim145Endpoint S d N D ≤
      CB * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) := by
    simpa [ActualClaim145BoundAt, caseIIOddClaim145Endpoint] using hB
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hlogLarge : 3 * A ≤ Real.log (D : ℝ) := by
    have hmax : max 1 (3 * A) ≤ Real.log (D : ℝ) := by
      apply (Real.le_log_iff_exp_le hD0).2
      exact hDlarge
    exact (le_max_right 1 (3 * A)).trans hmax
  have hcoordLarge : A ≤ (1 / 3 : ℝ) * Real.log (D : ℝ) := by linarith
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hrootD : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    have hexp : 1 / s ≤ (1 : ℝ) := by rw [div_le_one hs0]; exact hs1.le
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hDreal1.le hexp
  have hzDnat : z ≤ D := by dsimp [z]; exact Nat.ceil_le.mpr hrootD
  have hzD : (z : ℝ) ≤ (D : ℝ) := by exact_mod_cast hzDnat
  have hV := suzukiVProduct_mono_antitone S hzD
  have hsdomain : s ∈ KappaOneModel.parityDomain 2 N := by
    rw [KappaOneModel.parityDomain, Nat.odd_iff.mp hN]
    norm_num
    exact hs1
  have hEtransport := errorEnvelope_coordinate_transport_full
    hH.toSection13HatContract
    (N := N) (D := (D : ℝ)) (d := d) (σ := sourceSigma (D : ℝ) d)
    (x := s) (y := sourceSigma (D : ℝ) d)
    (by linarith) hDreal1 (by simpa [A] using hcoordLarge) hi hsdomain
    (hs3.trans g.h3σ) le_rfl
  have hEσ0 : 0 ≤ errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) :=
    errorEnvelope_nonneg H N hDreal1 (by linarith [g.h3σ])
      (hH.positive (ErrorSign.ofDepth N) _ (by linarith [g.h3σ])).le
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg (Real.log_pos hDreal1).le _
  have hVD : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    simpa [claim14_5VProduct, suzukiVProduct] using
      (suzukiVProduct_pos S (D : ℝ)).le
  have hVz : claim14_5VProduct S (D : ℝ) ≤ suzukiVProduct S (z : ℝ) := by
    simpa [claim14_5VProduct, suzukiVProduct] using hV
  have hconstBase := hconst3 (D : ℝ) hDconst
  have hconstant : CB ≤ 27 * C * (1 - Δ) * Real.log (D : ℝ) / 32 := by
    calc
      CB ≤ 27 * 3 * (1 - Δ) * Real.log (D : ℝ) / 32 := hconstBase
      _ ≤ 27 * C * (1 - Δ) * Real.log (D : ℝ) / 32 := by
        gcongr
  have hgapD := hgap C1 K N D hCgap hK hD2 hlarge hN hN3
  have hscale :
      CB * claim14_5Scale S H N (D : ℝ) d Δ
          (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d) ≤
        suzukiVProduct S (z : ℝ) *
          ((C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) *
            (1 - caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
              d Δ (sourceSigma (D : ℝ) d) K)) := by
    unfold claim14_5Scale
    simpa [z, mul_assoc] using claim145_endpoint_absorbed_by_caseII_gap
      hVD hVz (Real.exp_pos (Real.sqrt K)).le hEσ0 hEtransport hL
      (Real.log_pos hDreal1) (by linarith [g.h3σ]) hsrc.hDelta_lt.le
      hCB0.le (by linarith : 0 ≤ C) hgapD hconstant
  have hendpoint : caseIIOddClaim145Endpoint S d N D ≤
      suzukiVProduct S (z : ℝ) *
        ((C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) *
          (1 - caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
            d Δ (sourceSigma (D : ℝ) d) K)) := hendpointClaim.trans hscale
  dsimp [Lemma144CaseIISameCAt]
  simpa [sourceParityIndices, z] using
    (caseII_sameC_of_relative_and_endpoint_gap
      (scale := C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ))
      (bracket := caseIIConcreteRoundedRelativeBracketSourceLarge N (D : ℝ)
        d Δ (sourceSigma (D : ℝ) d) K)
      hendpoint hrelative)

/-- Compatibility wrapper for the original fixed-sieve moving Case-II API. -/
theorem exists_lemma144_caseII_odd_sameC_sourceLargeLog_uniform_moving
    (S : BoundingSieve) (H : Section13HatLayers)
    {Dmin : ℕ} {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (hDmin : 2 ≤ Dmin) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 C K : ℝ) (N D : ℕ) (s : ℝ),
        C1min ≤ C1 → 3 ≤ C → 2 ≤ K → 2 ≤ D →
        HasDimensionOneLocalProductBound S K →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Odd N → 3 ≤ N → 1 < s → s ≤ 3 →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (N - 1) Dmin →
        Lemma144CaseIISameCAt S H N D d Δ C K s := by
  obtain ⟨C1min, hC1min, hall⟩ :=
    exists_lemma144_caseII_odd_sameC_sourceLargeLog_uniform_moving_uniform_in_S
      H hH hsrc hDmin
  exact ⟨C1min, hC1min, hall S⟩


end MathlibNt.SieveTheory
