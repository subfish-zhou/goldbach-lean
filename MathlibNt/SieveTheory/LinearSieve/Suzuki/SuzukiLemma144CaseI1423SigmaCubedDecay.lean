import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Remainder1423

open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The literal `σ³ log (eσ)` scalar in (14.23) tends to zero in the
Case-I range.  This uses the explicit definition of `sourceSigma`; no limit
statement is assumed. -/
theorem tendsto_caseI1423_sourceScalar
    (K d Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    Tendsto (fun D : ℝ =>
      K ^ 2 * sourceSigma D d ^ 3 *
        Real.log (Real.exp 1 * sourceSigma D d) *
        Real.log (Real.log D) /
        (Real.log D) ^ (1 - Δ)) atTop (𝓝 0) := by
  have hβ : 0 < 1 - Δ := sub_pos.mpr hΔ1
  have hd0 : 0 < d := by
    have : 0 < 7 / (1 - Δ) := by positivity
    linarith
  have hd7 : 7 < d := by
    have hβlt : 1 - Δ < 1 := by linarith
    have hquot : 7 < 7 / (1 - Δ) := by
      apply (lt_div_iff₀ hβ).2
      nlinarith
    linarith
  have hinvd : 1 / d ≤ 1 := by
    have hd1 : 1 < d := by linarith
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd1
    norm_num at h ⊢
    exact h.le
  let γ : ℝ := 1 - Δ - 3 / d
  have hγ : 0 < γ := by
    have hrecip : 1 / d < (1 - Δ) / 7 := by
      have h := one_div_lt_one_div_of_lt
        (show 0 < 7 / (1 - Δ) by positivity) hd
      have heq : 1 / (7 / (1 - Δ)) = (1 - Δ) / 7 := by
        field_simp [ne_of_gt hβ]
      rwa [heq] at h
    have hthree : 3 / d < 3 * ((1 - Δ) / 7) := by
      rw [show 3 / d = 3 * (1 / d) by ring]
      linarith
    have hthreeβ : 3 * ((1 - Δ) / 7) < 1 - Δ := by
      nlinarith
    dsimp [γ]
    linarith
  let δ : ℝ := γ / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let C : ℝ := 32 * (K ^ 2 + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hdom0 := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hδ).bound
    (show 0 < 1 / C by positivity)
  have hdom : ∀ᶠ x : ℝ in atTop,
      C * (Real.log x) ^ 5 ≤ x ^ δ := by
    filter_upwards [hdom0, eventually_ge_atTop (Real.exp 1)] with x hx hxe
    have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxe
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    have hq0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxpow0 : 0 ≤ x ^ δ := Real.rpow_nonneg hx0 _
    change |(Real.log x) ^ (5 : ℝ)| ≤ (1 / C) * |x ^ δ| at hx
    rw [abs_of_nonneg (Real.rpow_nonneg hq0 _), abs_of_nonneg hxpow0] at hx
    norm_num [Real.rpow_natCast] at hx
    have hx' : (Real.log x) ^ 5 ≤ C⁻¹ * x ^ δ := hx
    have := mul_le_mul_of_nonneg_left hx' hC.le
    field_simp [ne_of_gt hC] at this
    exact this
  have hupper : ∀ᶠ D : ℝ in atTop,
      K ^ 2 * sourceSigma D d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma D d) *
          Real.log (Real.log D) /
          (Real.log D) ^ (1 - Δ) ≤
        (Real.log D) ^ (-δ) := by
    filter_upwards [Real.tendsto_log_atTop.eventually hdom,
      Real.tendsto_log_atTop.eventually_ge_atTop
        (max (Real.exp 1) (max (Real.log 27) 2)),
      eventually_ge_atTop (2 : ℝ)] with D hpow hxlarge hD2
    let x : ℝ := Real.log D
    let q : ℝ := Real.log x
    let ell : ℝ := Real.log (Real.log (27 * D))
    have hDpos : 0 < D := by linarith
    have hxrest : max (Real.exp 1) (max (Real.log 27) 2) ≤ x := by
      simpa [x] using hxlarge
    have hxe : Real.exp 1 ≤ x := (le_max_left _ _).trans hxrest
    have hx27 : Real.log 27 ≤ x :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hxrest)
    have hx2 : 2 ≤ x :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hxrest)
    have hx : 0 < x := (Real.exp_pos 1).trans_le hxe
    have hx1 : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hxe
    have hq1 : 1 ≤ q := by
      dsimp [q]
      simpa only [Real.log_exp] using
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hx hxe
    have hq : 0 < q := zero_lt_one.trans_le hq1
    have hlog27D : Real.log (27 * D) = Real.log 27 + x := by
      dsimp [x]
      rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
    have hinnerPos : 0 < Real.log (27 * D) := by
      rw [hlog27D]
      positivity
    have hell : 0 < ell := by
      dsimp [ell]
      apply Real.log_pos
      rw [hlog27D]
      have h27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      linarith
    have hinnerLower : x ≤ Real.log (27 * D) := by
      rw [hlog27D]
      have h27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
      linarith
    have hellLower : q ≤ ell := by
      dsimp [q, ell]
      exact Real.strictMonoOn_log.monotoneOn hx hinnerPos hinnerLower
    have hell1 : 1 ≤ ell := hq1.trans hellLower
    have hinnerUpper : Real.log (27 * D) ≤ 2 * x := by
      rw [hlog27D]
      linarith
    have hellUpper : ell ≤ 2 * q := by
      have h := Real.log_le_log hinnerPos hinnerUpper
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)] at h
      have hlog2le : Real.log 2 ≤ q := by
        dsimp [q]
        exact Real.strictMonoOn_log.monotoneOn (by norm_num) hx hx2
      dsimp [ell, q] at h ⊢
      linarith
    have hsigma : 0 < sourceSigma D d := by
      dsimp [sourceSigma, x, ell]
      positivity
    have hsigma1 : 1 ≤ sourceSigma D d := by
      dsimp [sourceSigma, x, ell]
      have hxp : 1 ≤ x ^ (1 / d) := Real.one_le_rpow hx1 (by positivity)
      have hxp0 : 0 ≤ x ^ (1 / d) := Real.rpow_nonneg hx.le _
      nlinarith [mul_le_mul hxp hell1 zero_le_one hxp0]
    have hlogScalar0 : 0 ≤ Real.log (Real.exp 1 * sourceSigma D d) := by
      apply Real.log_nonneg
      have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [mul_le_mul hexp1 hsigma1 zero_le_one (Real.exp_pos 1).le]
    have hlogScalar : Real.log (Real.exp 1 * sourceSigma D d) ≤ 3 * q := by
      have hlogell : Real.log ell ≤ ell - 1 :=
        Real.log_le_sub_one_of_pos hell
      have hexpand : Real.log (Real.exp 1 * sourceSigma D d) =
          1 + (1 / d) * q + Real.log ell := by
        rw [Real.log_mul (Real.exp_ne_zero 1) hsigma.ne', Real.log_exp]
        dsimp [sourceSigma]
        rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' hell.ne',
          Real.log_rpow hx]
        rw [show Real.log x = q by rfl]
        ring
      rw [hexpand]
      have hterm : (1 / d) * q ≤ q :=
        mul_le_of_le_one_left hq.le hinvd
      linarith
    have hellcube : ell ^ 3 ≤ 8 * q ^ 3 := by
      calc
        ell ^ 3 ≤ (2 * q) ^ 3 := by gcongr
        _ = 8 * q ^ 3 := by ring
    have hpacket : ell ^ 3 *
        Real.log (Real.exp 1 * sourceSigma D d) * q ≤ 32 * q ^ 5 := by
      calc
        ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q ≤
            (8 * q ^ 3) * (3 * q) * q := by gcongr
        _ ≤ 32 * q ^ 5 := by nlinarith [sq_nonneg (q ^ 2)]
    have hKpacket : K ^ 2 *
        (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) ≤
        C * q ^ 5 := by
      dsimp [C]
      have hqpow : 0 ≤ q ^ 5 := by positivity
      calc
        K ^ 2 * (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) ≤
            K ^ 2 * (32 * q ^ 5) := by gcongr
        _ ≤ 32 * (K ^ 2 + 1) * q ^ 5 := by nlinarith [sq_nonneg K]
    have hpow' : C * q ^ 5 ≤ x ^ δ := by simpa [x, q] using hpow
    have halgebra :
        K ^ 2 * sourceSigma D d ^ 3 *
            Real.log (Real.exp 1 * sourceSigma D d) *
            Real.log (Real.log D) /
            (Real.log D) ^ (1 - Δ) =
          K ^ 2 * x ^ (-γ) *
            (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) := by
      have hfront : x ^ (3 / d) / x ^ (1 - Δ) = x ^ (-γ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
        congr 1
        dsimp [γ]
        ring
      have hxpow3 : (x ^ (1 / d)) ^ 3 = x ^ (3 / d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        norm_num only [Nat.cast_ofNat]
        congr 1
        ring
      dsimp [sourceSigma, x, q, ell]
      rw [mul_pow, hxpow3]
      change K ^ 2 * (x ^ (3 / d) * ell ^ 3) *
          Real.log (Real.exp 1 * (x ^ (1 / d) * ell)) * q /
          x ^ (1 - Δ) = _
      rw [show K ^ 2 * (x ^ (3 / d) * ell ^ 3) *
          Real.log (Real.exp 1 * (x ^ (1 / d) * ell)) * q /
          x ^ (1 - Δ) =
        K ^ 2 * (x ^ (3 / d) / x ^ (1 - Δ)) *
          (ell ^ 3 * Real.log (Real.exp 1 * (x ^ (1 / d) * ell)) * q) by ring]
      rw [hfront]
    rw [halgebra]
    have hxneg0 : 0 ≤ x ^ (-γ) := Real.rpow_nonneg hx.le _
    calc
      K ^ 2 * x ^ (-γ) *
          (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q) =
        x ^ (-γ) * (K ^ 2 *
          (ell ^ 3 * Real.log (Real.exp 1 * sourceSigma D d) * q)) := by ring
      _ ≤ x ^ (-γ) * (C * q ^ 5) :=
        mul_le_mul_of_nonneg_left hKpacket hxneg0
      _ ≤ x ^ (-γ) * x ^ δ :=
        mul_le_mul_of_nonneg_left hpow' hxneg0
      _ = x ^ (-δ) := by
        rw [← Real.rpow_add hx]
        congr 1
        dsimp [δ]
        linarith
  have hlower : ∀ᶠ D : ℝ in atTop,
      0 ≤ K ^ 2 * sourceSigma D d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma D d) *
          Real.log (Real.log D) /
          (Real.log D) ^ (1 - Δ) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (2 : ℝ)] with D hxlarge hD2
    have hDpos : 0 < D := by linarith
    have hx : 0 < Real.log D := Real.log_pos (by linarith)
    have hq1 : 1 ≤ Real.log (Real.log D) := by
      simpa only [Real.log_exp] using
        Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hx hxlarge
    have hell1 : 1 ≤ Real.log (Real.log (27 * D)) := by
      have h27D : Real.log D ≤ Real.log (27 * D) := by
        have h27Dpos : 0 < 27 * D := mul_pos (by norm_num) hDpos
        apply Real.strictMonoOn_log.monotoneOn hDpos h27Dpos
        nlinarith
      have hlog27Dpos : 0 < Real.log (27 * D) := hx.trans_le h27D
      exact hq1.trans
        (Real.strictMonoOn_log.monotoneOn hx hlog27Dpos h27D)
    have hsigma1 : 1 ≤ sourceSigma D d := by
      dsimp [sourceSigma]
      have hlogD1 : 1 ≤ Real.log D :=
        (Real.one_le_exp (by norm_num)).trans hxlarge
      have hxp : 1 ≤ Real.log D ^ (1 / d) :=
        Real.one_le_rpow hlogD1 (by positivity)
      nlinarith [mul_le_mul hxp hell1 zero_le_one
        (Real.rpow_nonneg hx.le (1 / d))]
    have hlogsigma : 0 ≤ Real.log (Real.exp 1 * sourceSigma D d) := by
      apply Real.log_nonneg
      have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [mul_le_mul hexp1 hsigma1 zero_le_one (Real.exp_pos 1).le]
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (tendsto_rpow_neg_atTop hδ |>.comp Real.tendsto_log_atTop)
    hlower hupper

/-- Boundedness form required by the `Σ₁₁` endpoint source contract. -/
theorem caseI1423Sigma11SourceScalar_of_range
    (K d Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    CaseI1423Sigma11SourceScalar K d Δ := by
  refine ⟨1, zero_le_one, ?_⟩
  exact (tendsto_caseI1423_sourceScalar K d Δ hΔ0 hΔ1 hd).eventually
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))

/-- The `Σ₁₂` source contract has the same literal scalar and follows from the
same decay theorem. -/
theorem caseI1423Sigma12SourceScalar_of_range
    (K d Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d) :
    CaseI1423Sigma12SourceScalar K d Δ := by
  refine ⟨1, zero_le_one, ?_⟩
  exact (tendsto_caseI1423_sourceScalar K d Δ hΔ0 hΔ1 hd).eventually
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))


end MathlibNt.SieveTheory
