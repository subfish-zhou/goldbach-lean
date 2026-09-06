import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CommonScaleUniformCutoff
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceParameters
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointCoefficientUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIExactRatioCoefficients
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIIntegralTransportRelative

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology Asymptotics

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 3600000

/-!
# Case-II cutoff uniform in `K` on the source large-log branch

The fixed-`K` bracket is too coarse for the source quantifier order because it
replaces `1 + 3K/log D` by `1 + 3K`.  Here we retain the exact ratio in both
finite endpoint coefficients.  After the common-scale cancellation of the
cubic `q_D(3)` term, every endpoint is bounded by
`O(K^2 * sourceSigma(D,d)^2 * (log D)^(Δ-1))` after multiplying by the source
gap denominator.  The source inequality (14.4)

`2/Θ + 3/d < 1-Δ`

then gives one cutoff in `C1`, before arbitrary `K`, `D`, and odd depth `N`.
-/

/-- The natural-ceiling Case-II bracket.  As in the production rounded
assembler, natural ceilings occur in the discrete carrier; the analytic
coordinates here remain the exact real roots. -/
noncomputable def caseIIConcreteRoundedRelativeBracketSourceLarge
    (N : ℕ) (D d Δ σ K : ℝ) : ℝ :=
  (1 + 3 * K / Real.log D) *
      (1 - 1 / σ) ^ (1 - Δ) * perturbation D d 0 3 +
    caseIIEndpointRelativeCoeffSourceLarge N D Δ σ K

private theorem sourceLargeLog_core_decay
    {d Δ Θ : ℝ} (hsrc : SuzukiClaim145SourceParameters d Δ Θ)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧ ∀ (C1 K D : ℝ),
      C1min ≤ C1 → 2 ≤ K → 2 ≤ D → C1 * K ^ Θ < Real.log D →
      M * K ^ 2 * sourceSigma D d ^ 2 * (Real.log D) ^ (Δ - 1) ≤
        5 * (1 - Δ) / 32 := by
  let β : ℝ := 1 - Δ
  have hβ : 0 < β := sub_pos.mpr hsrc.hDelta_lt
  have hd : 0 < d := hsrc.d_pos
  have hΘ : 0 < Θ := hsrc.hTheta_pos
  let η : ℝ := β - (2 / Θ + 3 / d)
  have hη : 0 < η := by
    dsimp [η, β]
    linarith [hsrc.h14_4]
  let B : ℝ := max 1 (128 * M / (5 * β))
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB1
  let Xpow : ℝ := B ^ (1 / η)
  have hXpow0 : 0 ≤ Xpow := Real.rpow_nonneg hB0.le _
  have hdom0 :=
    (isLittleO_log_rpow_rpow_atTop 2 (show 0 < 1 / d by positivity)).bound
      (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.1 hdom0
  let C1min : ℝ := max (max 2 (Real.log 27)) (max Xlog Xpow)
  have hC1 : 1 ≤ C1min := by
    exact (show (1 : ℝ) ≤ 2 by norm_num).trans
      ((le_max_left 2 (Real.log 27)).trans (le_max_left _ _))
  refine ⟨C1min, hC1, ?_⟩
  intro C1 K D hC1C hK hD2 hlarge
  let x : ℝ := Real.log D
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKΘ1 : 1 ≤ K ^ Θ := Real.one_le_rpow hK1 hΘ.le
  have hxC1 : C1 < x := by
    calc
      C1 ≤ C1 * K ^ Θ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKΘ1
          (zero_le_one.trans (hC1.trans hC1C))
      _ < x := by simpa [x] using hlarge
  have hxMin : C1min < x := hC1C.trans_lt hxC1
  have hx2 : 2 < x :=
    (le_max_left 2 (Real.log 27)).trans_lt
      ((le_max_left (max 2 (Real.log 27)) _).trans_lt hxMin)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog27x : Real.log 27 ≤ x :=
    (le_max_right 2 (Real.log 27)).trans
      ((le_max_left (max 2 (Real.log 27)) _).trans hxMin.le)
  have hD1 : 1 < D := by linarith
  have hD0 : 0 < D := zero_lt_one.trans hD1
  have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hD0)]
  have hinner_le : Real.log (27 * D) ≤ 2 * x := by
    rw [hlog27D]
    linarith
  have hinner_pos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hll_le : Real.log (Real.log (27 * D)) ≤ 2 * Real.log x := by
    have h := Real.strictMonoOn_log.monotoneOn hinner_pos
      (show 0 < 2 * x by positivity) hinner_le
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx0)] at h
    have hlog2 : Real.log 2 ≤ Real.log x :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hx0 hx2.le
    linarith
  have hlogdom : (Real.log x) ^ 2 ≤ x ^ (1 / d) := by
    have hXlogMin : Xlog ≤ C1min :=
      (le_max_left Xlog Xpow).trans (le_max_right _ _)
    have h := hXlog x (hXlogMin.trans hxMin.le)
    change |Real.log x ^ (2 : ℝ)| ≤ 1 * |x ^ (1 / d)| at h
    rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at h
    exact h
  have hll0 : 0 ≤ Real.log (Real.log (27 * D)) := by
    have hinner1 : 1 ≤ Real.log (27 * D) := by
      rw [hlog27D]
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      linarith
    exact Real.log_nonneg hinner1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hllsq : Real.log (Real.log (27 * D)) ^ 2 ≤
      4 * (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (Real.log (27 * D)) - 2 * Real.log x)]
  have hsigSq : sourceSigma D d ^ 2 ≤ 4 * x ^ (3 / d) := by
    calc
      sourceSigma D d ^ 2 =
          (x ^ (1 / d)) ^ 2 * Real.log (Real.log (27 * D)) ^ 2 := by
        simp only [sourceSigma, x]
        ring
      _ ≤ (x ^ (1 / d)) ^ 2 * (4 * (Real.log x) ^ 2) := by
        gcongr
      _ ≤ (x ^ (1 / d)) ^ 2 * (4 * x ^ (1 / d)) := by
        gcongr
      _ = 4 * x ^ (3 / d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        calc
          x ^ (1 / d * (2 : ℝ)) * (4 * x ^ (1 / d)) =
              4 * (x ^ (1 / d * 2) * x ^ (1 / d)) := by ring
          _ = 4 * x ^ (1 / d * 2 + 1 / d) := by rw [Real.rpow_add hx0]
          _ = 4 * x ^ (3 / d) := by congr 2; ring
  have hKTheta : K ^ Θ < x := by
    calc
      K ^ Θ ≤ C1 * K ^ Θ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hC1.trans hC1C) (Real.rpow_nonneg hK0.le _)
      _ < x := by simpa [x] using hlarge
  have hKsq : K ^ 2 ≤ x ^ (2 / Θ) := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le Θ) hKTheta.le
      (show 0 ≤ 2 / Θ by positivity)
    calc
      K ^ 2 = (K ^ Θ) ^ (2 / Θ) := by
        rw [← Real.rpow_mul hK0.le]
        have : Θ * (2 / Θ) = 2 := by field_simp
        rw [this, Real.rpow_two]
      _ ≤ x ^ (2 / Θ) := hpow
  have hprod : K ^ 2 * sourceSigma D d ^ 2 ≤
      4 * x ^ (2 / Θ + 3 / d) := by
    calc
      K ^ 2 * sourceSigma D d ^ 2 ≤
          x ^ (2 / Θ) * (4 * x ^ (3 / d)) :=
        mul_le_mul hKsq hsigSq (sq_nonneg _) (Real.rpow_nonneg hx0.le _)
      _ = 4 * x ^ (2 / Θ + 3 / d) := by
        calc
          x ^ (2 / Θ) * (4 * x ^ (3 / d)) =
              4 * (x ^ (2 / Θ) * x ^ (3 / d)) := by ring
          _ = 4 * x ^ (2 / Θ + 3 / d) := by rw [Real.rpow_add hx0]
  have hdecay : x ^ (-η) ≤ 1 / B := by
    have hXpowMin : Xpow ≤ C1min :=
      (le_max_right Xlog Xpow).trans (le_max_right _ _)
    have hXpowx : Xpow ≤ x := hXpowMin.trans hxMin.le
    have hp := Real.rpow_le_rpow hXpow0 hXpowx hη.le
    have hpId : Xpow ^ η = B := by
      dsimp [Xpow]
      rw [← Real.rpow_mul hB0.le]
      have : (1 / η) * η = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [hpId] at hp
    have hxη : 0 < x ^ η := Real.rpow_pos_of_pos hx0 _
    rw [Real.rpow_neg hx0.le]
    simpa only [one_div] using one_div_le_one_div_of_le hB0 hp
  have hpowid :
      x ^ (2 / Θ + 3 / d) * x ^ (Δ - 1) = x ^ (-η) := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp [η, β]
    ring
  have hMB : 4 * M / B ≤ 5 * β / 32 := by
    have hcoef : 128 * M / (5 * β) ≤ B := le_max_right _ _
    have hscaled := mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ 5 * β / 32 by positivity)
    have hBpos : 0 < B := hB0
    apply (div_le_iff₀ hBpos).2
    calc
      4 * M = (128 * M / (5 * β)) * (5 * β / 32) := by
        field_simp
        ring
      _ ≤ B * (5 * β / 32) := hscaled
    nlinarith
  change M * K ^ 2 * sourceSigma D d ^ 2 * x ^ (Δ - 1) ≤ _
  calc
    M * K ^ 2 * sourceSigma D d ^ 2 * x ^ (Δ - 1) =
        M * (K ^ 2 * sourceSigma D d ^ 2) * x ^ (Δ - 1) := by ring
    _ ≤ M * (4 * x ^ (2 / Θ + 3 / d)) * x ^ (Δ - 1) := by
      gcongr
    _ = 4 * M * x ^ (-η) := by rw [← hpowid]; ring
    _ ≤ 4 * M * (1 / B) := by gcongr
    _ = 4 * M / B := by ring
    _ ≤ 5 * (1 - Δ) / 32 := by simpa [β] using hMB

private theorem perturbation_three_le_one_add_seven_ratio_sourceLarge
    {D d : ℝ} (hlog : 0 < Real.log D) (hd : 0 ≤ d)
    (hsmall : 3 ^ d ≤ Real.log D) :
    perturbation D d 0 3 ≤ 1 + 7 * (3 ^ d / Real.log D) := by
  exact perturbation_three_le_one_add_seven_ratio hlog hd hsmall

/-- Quantitative source-large-log replacement for the moving rounded Case-II
bracket.  The witness is a lower bound for the source separator `C1`; it is
chosen before arbitrary `K`, natural `D`, and odd recursion depth `N`.
The conclusion retains exactly `27/32` of the source contraction gap. -/
theorem exists_caseIIConcreteRoundedRelativeBracketSourceLarge_gap_uniform
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ Θ : ℝ} (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K : ℝ) (N D : ℕ),
        C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        C1 * K ^ Θ < Real.log (D : ℝ) → Odd N → 3 ≤ N →
        27 * (1 - Δ) / (32 * sourceSigma (D : ℝ) d) ≤
          1 - caseIIConcreteRoundedRelativeBracketSourceLarge
            N (D : ℝ) d Δ (sourceSigma (D : ℝ) d) K := by
  obtain ⟨L3, L2, hL3, hL2, hLayers⟩ := caseII_endpoint_source_layers_uniform hH
  let rΔ : ℝ := ((3 : ℝ) / 2) ^ Δ
  let p : ℝ := 3 ^ d
  let J : ℝ := 3 + 28 * p
  let M : ℝ := 9 * L3 + 72 * L2 + 864 * rΔ + 27 + J
  have hr0 : 0 ≤ rΔ := by dsimp [rΔ]; positivity
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hJ0 : 0 ≤ J := by dsimp [J]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨Cdec, hCdec, hdec⟩ := sourceLargeLog_core_decay hsrc M hM0
  let C1min : ℝ := max Cdec (max (Real.exp 1) p)
  have hCmin : 1 ≤ C1min := hCdec.trans (le_max_left _ _)
  refine ⟨C1min, hCmin, ?_⟩
  intro C1 K N D hC1 hK hD hlarge hN hN3
  let x : ℝ := Real.log (D : ℝ)
  let σ : ℝ := sourceSigma (D : ℝ) d
  let c : ℝ := (1 - 1 / σ) ^ (1 - Δ)
  have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD1 : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hDreal1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hD1
  have hx0 : 0 < x := by simpa [x] using Real.log_pos hDreal1
  have hCdecC : Cdec ≤ C1 := (le_max_left _ _).trans hC1
  have hxC : C1 < x := by
    have hK0 : 0 < K := by linarith
    have hKΘ1 : 1 ≤ K ^ Θ := Real.one_le_rpow (by linarith) hsrc.hTheta_pos.le
    calc
      C1 ≤ C1 * K ^ Θ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hKΘ1
          (zero_le_one.trans (hCmin.trans hC1))
      _ < x := by simpa [x] using hlarge
  have hxExp : Real.exp 1 < x :=
    ((le_max_left (Real.exp 1) p).trans (le_max_right Cdec _)).trans_lt
      (hC1.trans_lt hxC)
  have hxp : p < x :=
    ((le_max_right (Real.exp 1) p).trans (le_max_right Cdec _)).trans_lt
      (hC1.trans_lt hxC)
  have hx1 : 1 ≤ x := (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hxExp.le
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hKΘ : K ^ Θ < x := by
    calc
      K ^ Θ ≤ C1 * K ^ Θ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hCmin.trans hC1) (Real.rpow_nonneg hK0.le _)
      _ < x := by simpa [x] using hlarge
  have hTheta1 : 1 ≤ Θ := hsrc.one_le_theta
  have hKlePow : K ≤ K ^ Θ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK1 hTheta1
  have hKx : K ≤ x := hKlePow.trans hKΘ.le
  have hfac : 1 + 3 * K / x ≤ 4 := by
    have hratio : K / x ≤ 1 := (div_le_one hx0).2 hKx
    calc
      1 + 3 * K / x = 1 + 3 * (K / x) := by ring
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hfac0 : 0 ≤ 1 + 3 * K / x := by positivity
  have hDexp : Real.exp (Real.exp 1) ≤ (D : ℝ) := by
    apply (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < (D : ℝ))).mp
    simpa [x] using hxExp.le
  have hσ1 : 1 < σ := by
    simpa [σ, sourceSigma, SwitchingPrinciple.SuzukiLemma144KappaOne.sourceSigma] using
      SwitchingPrinciple.SuzukiLemma144KappaOne.sourceSigma_gt_one_of_large hsrc.d_pos hDexp
  have hσ0 : 0 < σ := zero_lt_one.trans hσ1
  have hc0 : 0 ≤ c := by
    dsimp [c]
    apply Real.rpow_nonneg
    rw [sub_nonneg, div_le_one hσ0]
    exact hσ1.le
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply Real.rpow_le_one
    · rw [sub_nonneg, div_le_one hσ0]
      exact hσ1.le
    · linarith [one_div_pos.mpr hσ0]
    · linarith [hsrc.hDelta_lt]
  have hpow0 : 0 ≤ x ^ (Δ - 1) := Real.rpow_nonneg hx0.le _
  have hinvpow : x⁻¹ ≤ x ^ (Δ - 1) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hsrc.hDelta_pos])
  obtain ⟨hLayer3, hLayer2⟩ := hLayers N hN hN3
  have hNm : (N - 1) % 2 = 0 := by
    have := Nat.odd_iff.mp hN
    omega
  have hLayer2nonneg : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hA0 :
      caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K ≤
        9 * K * L3 + 72 * K ^ 2 * σ * L2 := by
    unfold caseIIAlgebraicEndpointCoeffSourceLarge
    change 9 * K * finiteSourceLayer 1 2 N 3 +
      18 * K ^ 2 * σ * (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤ _
    have hfirst : 9 * K * finiteSourceLayer 1 2 N 3 ≤ 9 * K * L3 := by
      exact mul_le_mul_of_nonneg_left hLayer3 (by positivity)
    have hsecond :
        18 * K ^ 2 * σ * (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤
          72 * K ^ 2 * σ * L2 := by
      calc
        _ ≤ 18 * K ^ 2 * σ * 4 * L2 := by
          have hpos : 0 ≤ 18 * K ^ 2 * σ := by positivity
          have hterm2 : (1 + 3 * K / x) * finiteSourceLayer 1 2 (N - 1) 2 ≤ 4 * L2 :=
            mul_le_mul hfac hLayer2 hLayer2nonneg (by norm_num : (0 : ℝ) ≤ 4)
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm2 hpos
        _ = 72 * K ^ 2 * σ * L2 := by ring
    exact add_le_add hfirst hsecond
  have hQ :
      caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K ≤
        864 * K ^ 2 * rΔ := by
    unfold caseIIQDRelativeEndpointCoeffSourceLarge
    change 216 * K ^ 2 * (1 + 3 * K / x) * ((3 : ℝ) / 2) ^ Δ ≤ _
    calc
      _ ≤ 216 * K ^ 2 * 4 * rΔ := by gcongr
      _ = 864 * K ^ 2 * rΔ := by ring
  have hbaseUnit : 1 ≤ K * σ := by
    calc
      1 ≤ σ := hσ1.le
      _ ≤ K * σ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hK1 hσ0.le
  have hKsigma : K * σ ≤ K ^ 2 * σ ^ 2 := by
    calc
      K * σ = (K * σ) * 1 := by ring
      _ ≤ (K * σ) * (K * σ) :=
        mul_le_mul_of_nonneg_left hbaseUnit (mul_nonneg hK0.le hσ0.le)
      _ = K ^ 2 * σ ^ 2 := by ring
  let T : ℝ := K ^ 2 * σ ^ 2 * x ^ (Δ - 1)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hEndScaled :
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ ≤
        (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := by
    unfold caseIIEndpointRelativeCoeffSourceLarge
    change (caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) +
      σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x +
      27 * K * x ^ (Δ - 1)) * σ ≤ _
    have h0 : 9 * K * L3 * x ^ (Δ - 1) * σ ≤ 9 * L3 * T := by
      dsimp [T]
      have hL3pos : 0 ≤ 9 * L3 * x ^ (Δ - 1) := by positivity
      calc
        9 * K * L3 * x ^ (Δ - 1) * σ = (9 * L3 * x ^ (Δ - 1)) * (K * σ) := by ring
        _ ≤ (9 * L3 * x ^ (Δ - 1)) * (K ^ 2 * σ ^ 2) := mul_le_mul_of_nonneg_left hKsigma hL3pos
        _ = 9 * L3 * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    have h1 : 72 * K ^ 2 * σ * L2 * x ^ (Δ - 1) * σ = 72 * L2 * T := by
      dsimp [T]
      ring
    have hqinv :
        σ * (864 * K ^ 2 * rΔ) / x * σ ≤ 864 * rΔ * T := by
      rw [div_eq_mul_inv]
      dsimp [T]
      have h864pos : 0 ≤ 864 * rΔ * K ^ 2 * σ ^ 2 := by positivity
      calc
        σ * (864 * K ^ 2 * rΔ) * x⁻¹ * σ =
            864 * rΔ * K ^ 2 * σ ^ 2 * x⁻¹ := by ring
        _ ≤ 864 * rΔ * K ^ 2 * σ ^ 2 * x ^ (Δ - 1) := mul_le_mul_of_nonneg_left hinvpow h864pos
        _ = 864 * rΔ * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    have h2 : 27 * K * x ^ (Δ - 1) * σ ≤ 27 * T := by
      dsimp [T]
      have h27pos : 0 ≤ 27 * x ^ (Δ - 1) := by positivity
      calc
        27 * K * x ^ (Δ - 1) * σ = (27 * x ^ (Δ - 1)) * (K * σ) := by ring
        _ ≤ (27 * x ^ (Δ - 1)) * (K ^ 2 * σ ^ 2) := mul_le_mul_of_nonneg_left hKsigma h27pos
        _ = 27 * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
    calc
      (caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) +
          σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x +
          27 * K * x ^ (Δ - 1)) * σ =
        caseIIAlgebraicEndpointCoeffSourceLarge N (D : ℝ) σ K * x ^ (Δ - 1) * σ +
          σ * caseIIQDRelativeEndpointCoeffSourceLarge (D : ℝ) Δ K / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by ring
      _ ≤ (9 * K * L3 + 72 * K ^ 2 * σ * L2) * x ^ (Δ - 1) * σ +
          σ * (864 * K ^ 2 * rΔ) / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by
        gcongr
      _ = 9 * K * L3 * x ^ (Δ - 1) * σ +
          72 * K ^ 2 * σ * L2 * x ^ (Δ - 1) * σ +
          σ * (864 * K ^ 2 * rΔ) / x * σ +
          27 * K * x ^ (Δ - 1) * σ := by ring
      _ ≤ 9 * L3 * T + 72 * L2 * T + 864 * rΔ * T + 27 * T := by
        exact add_le_add (add_le_add (add_le_add h0 h1.le) hqinv) h2
      _ = (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := by ring
  have hpLog : 3 ^ d ≤ Real.log (D : ℝ) := by simpa [p, x] using hxp.le
  have hpert := perturbation_three_le_one_add_seven_ratio_sourceLarge
    (D := (D : ℝ)) (d := d) (by simpa [x] using hx0) hsrc.d_pos.le hpLog
  let fac : ℝ := 1 + 3 * K / x
  have hmainPert : fac * c * perturbation (D : ℝ) d 0 3 ≤
      fac * c * (1 + 7 * (p / x)) := by
    exact mul_le_mul_of_nonneg_left hpert (mul_nonneg hfac0 hc0)
  have hexcess : fac * (1 + 7 * (p / x)) - 1 ≤ J * K / x := by
    have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    have hxinv1 : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx1
    have hcross : x⁻¹ * x⁻¹ ≤ x⁻¹ := mul_le_of_le_one_left hxinv0 hxinv1
    dsimp [fac, J]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hcros := mul_le_mul_of_nonneg_left hcross
      (show 0 ≤ 21 * K * p by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hK1 (show 0 ≤ 7 * p by positivity)]
  have hIntegral :
      ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤
        J * T := by
    have hraw :
        (1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c ≤ J * K / x := by
      calc
        _ ≤ fac * c * (1 + 7 * (p / x)) - c := by
          simpa [fac] using sub_le_sub_right hmainPert c
        _ = c * (fac * (1 + 7 * (p / x)) - 1) := by ring
        _ ≤ fac * (1 + 7 * (p / x)) - 1 := by
          apply mul_le_of_le_one_left _ hc1
          have hfac1 : 1 ≤ fac := by
            have : 0 ≤ 3 * K / x := by positivity
            dsimp [fac]; linarith
          have hsecond1 : 1 ≤ 1 + 7 * (p / x) := by
            have : 0 ≤ 7 * (p / x) := by positivity
            linarith
          have := mul_le_mul hfac1 hsecond1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
          nlinarith
        _ ≤ J * K / x := hexcess
    have hs := mul_le_mul_of_nonneg_right hraw hσ0.le
    dsimp [T]
    calc
      ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤
          (J * K / x) * σ := hs
      _ = J * (K * σ) * x⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ J * (K ^ 2 * σ ^ 2) * x⁻¹ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKsigma (by positivity)) (by positivity)
      _ ≤ J * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) := mul_le_mul_of_nonneg_left hinvpow (by positivity)
      _ = J * (K ^ 2 * σ ^ 2 * x ^ (Δ - 1)) := by ring
  have hTotalScaled :
      (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
        ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) * σ ≤
          M * T := by
    have hEnd2 : caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ ≤
        (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T := hEndScaled
    have hInt2 : ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ ≤ J * T := hIntegral
    calc
      (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
        ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) * σ =
        caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K * σ +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) * σ := by ring
      _ ≤ (9 * L3 + 72 * L2 + 864 * rΔ + 27) * T + J * T := add_le_add hEnd2 hInt2
      _ = (9 * L3 + 72 * L2 + 864 * rΔ + 27 + J) * T := by ring
      _ = M * T := by rfl
  have hCore := hdec C1 K (D : ℝ) hCdecC hK hDreal hlarge
  have hCore' : M * T ≤ 5 * (1 - Δ) / 32 := by
    have hTotal : M * T = M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) := by
      dsimp [T]
      ring
    have hCoreRe : M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) ≤ 5 * (1 - Δ) / 32 := by
      have hd1 : M * (K ^ 2 * σ ^ 2) * x ^ (Δ - 1) = M * K ^ 2 * σ ^ 2 * x ^ (Δ - 1) := by ring
      rw [hd1]
      exact hCore
    rw [hTotal]
    exact hCoreRe
  have hExcess :
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) ≤
        5 * (1 - Δ) / (32 * σ) := by
    apply (le_div_iff₀ (show 0 < 32 * σ by positivity)).2
    nlinarith [hTotalScaled.trans hCore']
  have hGap : (1 - Δ) / σ ≤ 1 - c := by
    simpa [c] using rpow_contraction_gap
      hsrc.hDelta_pos hsrc.hDelta_lt hσ1
  change 27 * (1 - Δ) / (32 * σ) ≤
    1 - ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 +
      caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K)
  have ht : caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K +
          ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c) ≤
        5 * (1 - Δ) / (32 * σ) := hExcess
  calc
    27 * (1 - Δ) / (32 * σ) = (1 - Δ) / σ - 5 * (1 - Δ) / (32 * σ) := by ring
    _ ≤ 1 - c - 5 * (1 - Δ) / (32 * σ) := by linarith [hGap]
    _ ≤ 1 - c - (caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K + ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 - c)) := by linarith [ht]
    _ = 1 - ((1 + 3 * K / x) * c * perturbation (D : ℝ) d 0 3 + caseIIEndpointRelativeCoeffSourceLarge N (D : ℝ) Δ σ K) := by ring


end MathlibNt.SieveTheory
