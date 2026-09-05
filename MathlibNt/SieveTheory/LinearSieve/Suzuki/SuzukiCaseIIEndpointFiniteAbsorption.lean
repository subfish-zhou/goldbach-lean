import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointQuantitative

open scoped Classical BigOperators Interval
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- The three non-integral pieces of the transported Case-II endpoint error,
with the integral in `caseIIEndpointQD` omitted.  The power coordinates are
kept as real variables so that their exact logarithmic identities can be used. -/
noncomputable def caseIINonIntegralEndpointCorrections
    (H : Section13HatLayers) (N : ℕ) (D y w d Δ σ C K s : ℝ) : ℝ :=
  (3 / s) * (K / Real.log y) * finiteSourceLayer 1 2 N 3 +
  (3 / s) * (1 + K / Real.log y) *
    ((6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 / Real.log w) * (3 / 3)) +
  (3 / s) * (1 + K / Real.log y) *
    (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
      ((6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ 3 /
        Real.log w) * (3 / 3)))

/-- A named coefficient for the two endpoint terms which do not intrinsically
carry the factor `(log D)^(-Δ)`. -/
noncomputable def caseIIAlgebraicEndpointCoeff
    (N : ℕ) (σ K : ℝ) : ℝ :=
  9 * K * finiteSourceLayer 1 2 N 3 +
    18 * K ^ 2 * σ * (1 + 3 * K) * finiteSourceLayer 1 2 (N - 1) 2

/-- A named coefficient for the cubic `q_D(3)/log w` endpoint term. -/
noncomputable def caseIIQDEndpointCoeff
    (d Δ σ C K : ℝ) : ℝ :=
  72 * K ^ 2 * σ * (1 + 3 * K) * C * Real.exp (Real.sqrt K) *
    ((3 : ℝ) / 2) ^ Δ

/-- Exact, uniform estimates for all three non-integral endpoint corrections.

The first conclusion is the sharp scale actually supplied by the product-ratio
and `Σ₁₁` terms, namely `1 / log D`.  The second conclusion has the additional
`(log D)^(-Δ)` because that factor is present in `caseIIEndpointQD` itself. -/
theorem caseII_nonIntegral_endpoint_corrections_separate
    {H : Section13HatLayers} {N : ℕ} {D y w d Δ σ C K s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ D)
    (hy : y = D ^ (1 / (3 : ℝ))) (hw : w = D ^ (1 / σ))
    (hσ : 0 < σ) (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : (3 : ℝ) ^ d ≤ Real.log D) :
    (3 / s) * (K / Real.log y) * finiteSourceLayer 1 2 N 3 +
        (3 / s) * (1 + K / Real.log y) *
          ((6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 / Real.log w) * (3 / 3))
      ≤ caseIIAlgebraicEndpointCoeff N σ K / Real.log D ∧
    (3 / s) * (1 + K / Real.log y) *
        (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
          ((6 * K ^ 2 * qD H (ErrorSign.ofDepth N).opposite D d Δ 3 /
            Real.log w) * (3 / 3)))
      ≤ caseIIQDEndpointCoeff d Δ σ C K / Real.log D *
          (Real.log D) ^ (-Δ) := by
  have hD1 : 1 < D := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hlog1 : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hD
  have hs : 0 < s := zero_lt_one.trans hs1
  have hthree_s : 0 ≤ 3 / s := div_nonneg (by norm_num) hs.le
  have hthree_s_le : 3 / s ≤ 3 := by
    apply (div_le_iff₀ hs).2
    nlinarith
  have hFy : 0 ≤ finiteSourceLayer 1 2 N 3 :=
    caseII_finiteSourceLayer_three_nonneg hN
  have hNm : (N - 1) % 2 = 0 := by
    have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
    omega
  have hFw : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
    apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
    simp [KappaOneModel.parityDomain, hNm]
  have hylog := one_div_log_cubic_endpoint hD1 hy
  have hwlog := one_div_log_sigma_endpoint hD1 hσ hw
  have hyinv : (Real.log y)⁻¹ = 3 / Real.log D := by
    simpa only [one_div] using hylog
  have hwinv : (Real.log w)⁻¹ = σ / Real.log D := by
    simpa only [one_div] using hwlog
  have hKlog : 0 ≤ K / Real.log D := div_nonneg hK hlog.le
  have hKlog_le : K / Real.log D ≤ K := by
    exact (div_le_iff₀ hlog).2 (by nlinarith [mul_le_mul_of_nonneg_left hlog1 hK])
  have hfac_nonneg : 0 ≤ 1 + K * (3 / Real.log D) := by positivity
  have hfac_le : 1 + K * (3 / Real.log D) ≤ 1 + 3 * K := by
    calc
      1 + K * (3 / Real.log D) = 1 + 3 * (K / Real.log D) := by ring
      _ ≤ 1 + 3 * K :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hKlog_le (by norm_num))
  have hratio :
      (3 / s) * (K / Real.log y) * finiteSourceLayer 1 2 N 3 ≤
        (9 * K * finiteSourceLayer 1 2 N 3) / Real.log D := by
    rw [div_eq_mul_inv K (Real.log y), hyinv]
    calc
      (3 / s) * (K * (3 / Real.log D)) * finiteSourceLayer 1 2 N 3
          ≤ 3 * (K * (3 / Real.log D)) * finiteSourceLayer 1 2 N 3 := by
            gcongr
      _ = (9 * K * finiteSourceLayer 1 2 N 3) / Real.log D := by ring
  have hsigma :
      (3 / s) * (1 + K / Real.log y) *
          ((6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 / Real.log w) * (3 / 3)) ≤
        (18 * K ^ 2 * σ * (1 + 3 * K) *
          finiteSourceLayer 1 2 (N - 1) 2) / Real.log D := by
    rw [div_eq_mul_inv K (Real.log y), hyinv,
      div_eq_mul_inv (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2) (Real.log w),
      hwinv]
    norm_num
    have hab : (3 / s) * (1 + K * (3 / Real.log D)) ≤
        3 * (1 + 3 * K) :=
      mul_le_mul hthree_s_le hfac_le hfac_nonneg (by norm_num)
    have hc : 0 ≤ 6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 *
        (σ / Real.log D) := by positivity
    calc
      (3 / s) * (1 + K * (3 / Real.log D)) *
          (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * (σ / Real.log D))
        ≤ 3 * (1 + 3 * K) *
          (6 * K ^ 2 * finiteSourceLayer 1 2 (N - 1) 2 * (σ / Real.log D)) :=
            mul_le_mul_of_nonneg_right hab hc
      _ = (18 * K ^ 2 * σ * (1 + 3 * K) *
          finiteSourceLayer 1 2 (N - 1) 2) / Real.log D := by ring
  constructor
  · unfold caseIIAlgebraicEndpointCoeff
    calc
      _ ≤ (9 * K * finiteSourceLayer 1 2 N 3) / Real.log D +
          (18 * K ^ 2 * σ * (1 + 3 * K) *
            finiteSourceLayer 1 2 (N - 1) 2) / Real.log D :=
        add_le_add hratio hsigma
      _ = _ := by ring
  · have hq := qD_opposite_three_eq_of_odd hH hN (D := D) (d := d) (Δ := Δ)
    rw [hq]
    have hx0 : 0 ≤ (3 : ℝ) ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (by norm_num) d) hlog.le
    have hx1 : (3 : ℝ) ^ d / Real.log D ≤ 1 := (div_le_one hlog).2 hsmall
    have hsquare : (1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) ≤ 4 := by
      nlinarith [sq_nonneg ((3 : ℝ) ^ d / Real.log D - 1)]
    rw [div_eq_mul_inv K (Real.log y), hyinv,
      div_eq_mul_inv (6 * K ^ 2 *
        ((1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ))
        (Real.log w), hwinv]
    norm_num
    unfold caseIIQDEndpointCoeff
    have hrpow : 0 ≤ ((3 : ℝ) / 2) ^ Δ := Real.rpow_nonneg (by norm_num) Δ
    have hscale : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog.le (-Δ)
    have hab : (3 / s) * (1 + K * (3 / Real.log D)) ≤
        3 * (1 + 3 * K) :=
      mul_le_mul hthree_s_le hfac_le hfac_nonneg (by norm_num)
    have hc0 : 0 ≤ C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
        (6 * K ^ 2 *
          ((1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ) *
            (σ / Real.log D)) := by positivity
    have hc : C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
        (6 * K ^ 2 *
          ((1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ) *
            (σ / Real.log D)) ≤
        C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
        (6 * K ^ 2 * (4 * ((3 : ℝ) / 2) ^ Δ) *
          (σ / Real.log D)) := by
      gcongr
    calc
      (3 / s) * (1 + K * (3 / Real.log D)) *
          (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
            (6 * K ^ 2 *
              ((1 + (3 : ℝ) ^ d / Real.log D) ^ (2 : ℕ) * ((3 : ℝ) / 2) ^ Δ) *
                (σ / Real.log D)))
        ≤ 3 * (1 + 3 * K) *
          (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
            (6 * K ^ 2 * (4 * ((3 : ℝ) / 2) ^ Δ) *
              (σ / Real.log D))) :=
            mul_le_mul hab hc hc0 (by positivity)
      _ = (72 * K ^ 2 * σ * (1 + 3 * K) * C * Real.exp (Real.sqrt K) *
            ((3 : ℝ) / 2) ^ Δ) / Real.log D * (Real.log D) ^ (-Δ) := by ring

/-- Combining the preceding exact estimates with the odd Case-II lower bound
for `errorEnvelope`.  The extra premise is displayed because it is precisely
what is needed to put the product-ratio and `Σ₁₁` terms at the stronger
`(log D)^(-1-Δ)` scale. -/
theorem caseII_nonIntegral_endpoint_corrections_absorb
    {H : Section13HatLayers} {N : ℕ} {D y w d Δ σ C K s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ D)
    (hy : y = D ^ (1 / (3 : ℝ))) (hw : w = D ^ (1 / σ))
    (hσ : 0 < σ) (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : (3 : ℝ) ^ d ≤ Real.log D)
    (hScale : 1 ≤ (Real.log D) ^ (-Δ)) :
    caseIINonIntegralEndpointCorrections H N D y w d Δ σ C K s ≤
      (3 * (caseIIAlgebraicEndpointCoeff N σ K +
        caseIIQDEndpointCoeff d Δ σ C K)) / Real.log D *
        errorEnvelope H N D d s * (Real.log D) ^ (-Δ) := by
  rcases caseII_nonIntegral_endpoint_corrections_separate (Δ := Δ)
    hH hN hD hy hw hσ hs1 hs3 hK hC hsmall with ⟨halg, hq⟩
  have hD1 : 1 < D := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hlog : 0 < Real.log D := Real.log_pos hD1
  have hE := one_third_le_errorEnvelope_caseII (d := d) hH hN hD1 hs1 hs3
  have hA0 : 0 ≤ caseIIAlgebraicEndpointCoeff N σ K := by
    unfold caseIIAlgebraicEndpointCoeff
    have hFy := caseII_finiteSourceLayer_three_nonneg hN
    have hNm : (N - 1) % 2 = 0 := by
      have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
      omega
    have hFw : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
      apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
      simp [KappaOneModel.parityDomain, hNm]
    positivity
  have hAq : 0 ≤ caseIIQDEndpointCoeff d Δ σ C K := by
    unfold caseIIQDEndpointCoeff
    positivity
  have hscale0 : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlog.le (-Δ)
  have hcoeff : 0 ≤ caseIIAlgebraicEndpointCoeff N σ K / Real.log D :=
    div_nonneg hA0 hlog.le
  unfold caseIINonIntegralEndpointCorrections
  calc
    _ ≤ caseIIAlgebraicEndpointCoeff N σ K / Real.log D +
        caseIIQDEndpointCoeff d Δ σ C K / Real.log D *
          (Real.log D) ^ (-Δ) := add_le_add halg hq
    _ ≤ (caseIIAlgebraicEndpointCoeff N σ K +
          caseIIQDEndpointCoeff d Δ σ C K) / Real.log D *
          (Real.log D) ^ (-Δ) := by
      calc
        _ ≤ caseIIAlgebraicEndpointCoeff N σ K / Real.log D *
              (Real.log D) ^ (-Δ) +
            caseIIQDEndpointCoeff d Δ σ C K / Real.log D *
              (Real.log D) ^ (-Δ) := by
          have hfirst : caseIIAlgebraicEndpointCoeff N σ K / Real.log D ≤
              caseIIAlgebraicEndpointCoeff N σ K / Real.log D *
                (Real.log D) ^ (-Δ) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hScale hcoeff
          exact add_le_add hfirst le_rfl
        _ = _ := by ring
    _ ≤ (3 * (caseIIAlgebraicEndpointCoeff N σ K +
          caseIIQDEndpointCoeff d Δ σ C K)) / Real.log D *
          errorEnvelope H N D d s * (Real.log D) ^ (-Δ) := by
      have hsum : 0 ≤ (caseIIAlgebraicEndpointCoeff N σ K +
          caseIIQDEndpointCoeff d Δ σ C K) / Real.log D :=
        div_nonneg (add_nonneg hA0 hAq) hlog.le
      have h3E : 1 ≤ 3 * errorEnvelope H N D d s := by linarith
      let X : ℝ := (caseIIAlgebraicEndpointCoeff N σ K +
        caseIIQDEndpointCoeff d Δ σ C K) / Real.log D *
          (Real.log D) ^ (-Δ)
      have hX : 0 ≤ X := by
        dsimp [X]
        positivity
      have hm : X * 1 ≤ X * (3 * errorEnvelope H N D d s) :=
        mul_le_mul_of_nonneg_left h3E hX
      calc
        _ = X * 1 := by dsimp [X]; ring
        _ ≤ X * (3 * errorEnvelope H N D d s) := hm
        _ = _ := by dsimp [X]; ring


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
