import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedQuadraticConditionalErrorAssembly

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogDerivativeBound
open DirichletLGlobalConductorLogValueBound

local notation "𝓜" => mellin

/-- On either horizontal edge of the quadratic Perron rectangle, the
logarithmic derivative is bounded by twice the left-band budget.  The part to
the right of `1` is paid by transporting the annular lower bound at `1` over
the quarter-width extension. -/
theorem norm_logDerivative_le_on_quadraticConditionalPerronHorizontal
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T σ t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hc : 0 < c) (hη : 0 < η) (hT : 3 ≤ T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (ht : |t| = T)
    (hσleft : dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T ≤ σ)
    (hσright : σ ≤ dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T) :
    ‖deriv χ.LFunction (σ + I * t) / χ.LFunction (σ + I * t)‖ ≤
      2 * ((128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
          (c * (q : ℝ) ^ (-η)) +
        dirichletLQuadraticConditionalFixedH q
            (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
          (A * (q : ℝ) ^ (-2 * η))) := by
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let H := dirichletLQuadraticConditionalFixedH q τ T
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let x : ℝ := A * p / H ^ 12
  have hT0 : 0 < T := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcentralH : 0 < dirichletLQuadraticConditionalCentralH q T := by
    dsimp only [dirichletLQuadraticConditionalCentralH]
    have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
      exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
        unfold dirichletLNonquadraticConductorLogCutoff
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
          unfold dirichletLNonquadraticConductorLogHeightBlock
          omega)))
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < τ := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT0 (div_pos (mul_pos hc (Real.rpow_pos_of_pos hq _))
      (mul_pos (by norm_num) (sq_pos_of_pos hcentralH)))
  have hτT : τ ≤ T := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact min_le_left _ _
  have htlow : τ ≤ |t| := by rw [ht]; exact hτT
  have htT : |t| ≤ T := ht.le
  have hfixed : dirichletLQuadraticConditionalPowerZeroFreeH q t ≤ H := by
    simpa only [H, τ] using
      dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH hτ hτT htlow htT
  have hH1 : 1 ≤ H :=
    (one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t).trans hfixed
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hp : 0 < p := by
    dsimp only [p]
    exact Real.rpow_pos_of_pos hq _
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp only [x]
    exact (div_le_self (mul_nonneg hA.le hp.le) (one_le_pow₀ hH1)).trans
      ((mul_le_of_le_one_right hA.le hp1).trans hAhalf)
  have hleft : dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T = 1 - x := by
    rfl
  have hright : dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T =
      1 + x / 4 := by rfl
  by_cases hσone : σ ≤ 1
  · have hband := norm_logDerivative_le_on_quadraticConditionalWholeBand
      Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη hT0 hSiegel
      (by simpa only [dirichletLTwistedSmoothedQuadraticConditionalLeft] using hσleft)
      hσone htT
    exact hband.trans (by
      have hcentral : 0 ≤ (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
          (c * (q : ℝ) ^ (-η)) := by positivity
      have hann : 0 ≤ H ^ 12 / (A * p) := by positivity
      dsimp only [H, p, τ] at hann ⊢
      nlinarith)
  · have hσone' : 1 ≤ σ := le_of_not_ge hσone
    have hσtwo : σ ≤ 2 := by
      rw [hright] at hσright
      linarith
    have hnear1 : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ 1 :=
      sub_le_self _ (one_div_pos.mpr (log_conductorHeightCutoff_pos χ hχ t)).le
    have hlog0 : 0 ≤ 1 + Real.log (dirichletLConductorHeightCutoff q t) := by
      linarith [log_conductorHeightCutoff_pos χ hχ t]
    have hlogH : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H :=
      (one_add_log_conductorHeightCutoff_le_quadraticH q t).trans hfixed
    have hlower1 : 64 * H ^ 2 * x ≤ ‖χ.LFunction (1 + I * t)‖ := by
      have h := norm_LFunction_ge_on_quadraticConditionalAnnulus
        Z hZ hzeta χ hquad hχ hA hAhalf hAsmall hη hτ hτT
        (β := 1) (t := t) (by
          dsimp only [dirichletLQuadraticConditionalFixedLeft, x, p, H, τ]
          linarith) (le_refl 1) htlow htT
      change 64 * H ^ 2 * x ≤ ‖χ.LFunction (1 + I * t)‖
      convert h using 1; push_cast; ring
    have hdiff0 := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
      χ hχ (σ₁ := 1) (σ₂ := σ) (t := t) (by norm_num) hnear1 hσone' hσtwo
    have hdiff : ‖χ.LFunction (σ + I * t) - χ.LFunction (1 + I * t)‖ ≤
        16 * H ^ 2 * x := by
      calc
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
            (σ - 1) := by convert hdiff0 using 1; push_cast; ring
        _ ≤ 64 * H ^ 2 * (x / 4) := by
          rw [hright] at hσright
          apply mul_le_mul
          · gcongr
          · linarith
          · linarith
          · positivity
        _ = 16 * H ^ 2 * x := by ring
    have hlowerσ : 48 * H ^ 2 * x ≤ ‖χ.LFunction (σ + I * t)‖ := by
      have htri := norm_add_le
        (χ.LFunction (1 + I * t) - χ.LFunction (σ + I * t))
        (χ.LFunction (σ + I * t))
      rw [sub_add_cancel, norm_sub_rev] at htri
      linarith only [hlower1, hdiff, htri]
    have hnearσ : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ :=
      hnear1.trans hσone'
    have hderiv :=
      norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
        χ hχ (σ := σ) (t := t) (by linarith) hσtwo hnearσ
    have hderivH : ‖deriv χ.LFunction (σ + I * t)‖ ≤ 64 * H ^ 2 :=
      hderiv.trans (by gcongr)
    have hquot : ‖deriv χ.LFunction (σ + I * t) / χ.LFunction (σ + I * t)‖ ≤
        2 / x := by
      rw [norm_div]
      calc
        _ ≤ (64 * H ^ 2) / (48 * H ^ 2 * x) :=
          div_le_div₀ (by positivity) hderivH (by positivity) hlowerσ
        _ ≤ 2 / x := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_pos_of_pos hH]
    calc
      _ ≤ 2 / x := hquot
      _ = 2 * (H ^ 12 / (A * p)) := by
        dsimp only [x]
        field_simp [hA.ne', hp.ne', hH.ne']
      _ ≤ 2 * ((128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
            (c * (q : ℝ) ^ (-η)) + H ^ 12 / (A * p)) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by norm_num)
      _ = _ := by rfl

/-- Genuine Bochner norms for the left and both horizontal edges of the
quadratic conditional rectangle. -/
theorem exists_dirichletLTwistedSmoothedQuadraticConditionalContourNormBounds
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : support ν ⊆ Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (Z : ℝ), 0 < Z →
      (∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
        ‖riemannZeta (1 + x + I * u)‖ ≤
          Z * (1 + Real.log (|u| + 2) + 1 / |u|)) →
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
        {A c η T ε X : ℝ}, χ ^ 2 = 1 → χ ≠ 1 →
        0 < A → A ≤ c / 256 → A ≤ 1 / 2 →
        A ≤ 1 / (16 * Z * 192 ^ 4) → 0 < c → 0 < η → 3 ≤ T →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        0 < ε → ε < 1 → 1 ≤ X →
        let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
              (c * (q : ℝ) ^ (-η)) +
            dirichletLQuadraticConditionalFixedH q
                (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
              (A * (q : ℝ) ^ (-2 * η))
        let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
        let b := dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T
        ‖VIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a (-T) T‖ ≤ C * T * Q * X ^ a / ε ∧
        ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a b T‖ ≤ C * Q * X ^ b / (ε * (1 + T ^ 2)) ∧
        ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
            a b (-T)‖ ≤ C * Q * X ^ b / (ε * (1 + T ^ 2)) := by
  obtain ⟨M, hM, hMellin⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨16 * M, by positivity, ?_⟩
  intro Z hZ hzeta q _ χ A c η T ε X hquad hχ hA hAc hAhalf hAsmall hc hη hT
    hSiegel hε hε1 hX
  dsimp only
  let Q := (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
        (c * (q : ℝ) ^ (-η)) +
      dirichletLQuadraticConditionalFixedH q
          (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
        (A * (q : ℝ) ^ (-2 * η))
  let a := dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T
  let b := dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := by linarith
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hcentralH : 0 < dirichletLQuadraticConditionalCentralH q T := by
    dsimp only [dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have htau : 0 < dirichletLQuadraticConditionalCentralHeight c η q T := by
    dsimp only [dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT0 (div_pos (mul_pos hc (Real.rpow_pos_of_pos hq _))
      (mul_pos (by norm_num) (sq_pos_of_pos hcentralH)))
  have hH1 : 1 ≤ dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T := by
    dsimp only [dirichletLQuadraticConditionalFixedH]
    have hlog : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T) :=
      Real.log_nonneg hcut
    have hlogT : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
    have hinv : 0 < 1 / (2 * dirichletLQuadraticConditionalCentralHeight c η q T) := by
      positivity
    linarith
  have hH : 0 < dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T :=
    lt_of_lt_of_le zero_lt_one hH1
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T := by
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    positivity
  have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hpow : 1 ≤ dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 := one_le_pow₀ hH1
  have hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2 := by
    dsimp only [dirichletLQuadraticConditionalCrossZeroWidth]
    calc
      A * (q : ℝ) ^ (-2 * η) /
          dirichletLQuadraticConditionalFixedH q
              (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 ≤ A := by
        exact (div_le_self (by positivity) hpow).trans
          (mul_le_of_le_one_right hA.le hp1)
      _ ≤ 1 / 2 := hAhalf
  have ha : (1 / 2 : ℝ) ≤ a := by
    dsimp only [a, dirichletLTwistedSmoothedQuadraticConditionalLeft]
    linarith
  have hb : b ≤ 2 := by
    dsimp only [b, dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta]
    linarith
  have hab : a ≤ b := by
    dsimp only [a, b, dirichletLTwistedSmoothedQuadraticConditionalLeft,
      dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta]
    linarith
  have verticalPoint (t : ℝ) (ht' : |t| ≤ T) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖ ≤
        Q * (4 * M / ε) * X ^ a := by
    have hlog := norm_logDerivative_le_on_quadraticConditionalPerronLeft
      Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη hT0 hSiegel hw ht'
    have hm := hMellin (1 / 2) (by norm_num) (a + t * I)
      (by simp; norm_num at ha ⊢; exact ha) (by simp; exact (hab.trans hb)) ε hε hε1
    have hnormsq : (1 / 4 : ℝ) ≤ ‖(a : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith [sq_nonneg t]
    have hm' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (a + t * I)‖ ≤ 4 * M / ε := by
      calc
        _ ≤ M * (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (ε * (1 / 4))⁻¹ := by gcongr
        _ = 4 * M / ε := by field_simp
    have hXnorm : ‖(X : ℂ) ^ ((a : ℂ) + t * I)‖ = X ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    have hlog' : ‖-deriv χ.LFunction (a + t * I) / χ.LFunction (a + t * I)‖ ≤ Q := by
      simpa only [neg_div, norm_neg, a, Q, mul_comm] using hlog
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hlog' hm' (norm_nonneg _) (by positivity)) (Real.rpow_nonneg hX0.le _)
  have horizontalPoint (σ t : ℝ) (hσa : a ≤ σ) (hσb : σ ≤ b) (ht' : |t| = T) :
      ‖DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)‖ ≤
        (2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ b := by
    have hlog := norm_logDerivative_le_on_quadraticConditionalPerronHorizontal
      Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη hT hSiegel ht'
      (by simpa only [a] using hσa) (by simpa only [b] using hσb)
    have hm := hMellin (1 / 2) (by norm_num) (σ + t * I)
      (by simp; linarith) (by simp; exact hσb.trans hb) ε hε hε1
    have hnormsq : T ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      have ht2 := congrArg (fun u : ℝ => u ^ 2) ht'
      rw [sq_abs] at ht2
      nlinarith [sq_nonneg σ]
    have hinvDen : (T ^ 2)⁻¹ ≤ 2 * (1 + T ^ 2)⁻¹ := by
      rw [show (T ^ 2)⁻¹ = 1 / T ^ 2 by rw [one_div],
        show 2 * (1 + T ^ 2)⁻¹ = 2 / (1 + T ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ (sq_pos_of_pos hT0) (by positivity)]
      nlinarith [sq_nonneg T]
    have hm' : ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤
        2 * M / (ε * (1 + T ^ 2)) := by
      calc
        _ ≤ M * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (2 / (ε * (1 + T ^ 2))) := by
          gcongr
          rw [mul_inv_rev]
          calc
            (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤
                (2 * (1 + T ^ 2)⁻¹) * ε⁻¹ := by
              gcongr
              exact (inv_anti₀ (sq_pos_of_pos hT0) hnormsq).trans hinvDen
            _ = 2 / (ε * (1 + T ^ 2)) := by field_simp [hε.ne']
        _ = 2 * M / (ε * (1 + T ^ 2)) := by ring
    have hXnorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hXpow : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσb
    dsimp only [DirichletCharacter.twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    have hlog' : ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤
        2 * Q := by
      simpa only [neg_div, norm_neg, Q, mul_comm] using hlog
    calc
      _ ≤ (2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ σ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hlog' hm' (norm_nonneg _) (by positivity)) (Real.rpow_nonneg hX0.le _)
      _ ≤ _ := by gcongr
  have hvertical : ‖VIntegral
      (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X) a (-T) T‖ ≤
      (16 * M) * T * Q * X ^ a / ε := by
    rw [VIntegral, norm_smul, norm_I, one_mul]
    calc
      _ ≤ (Q * (4 * M / ε) * X ^ a) * |T - (-T)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht'
        rw [uIoc_of_le (by linarith)] at ht'
        apply verticalPoint t
        rw [abs_le]
        exact ⟨ht'.1.le, ht'.2⟩
      _ ≤ (16 * M) * T * Q * X ^ a / ε := by
        rw [abs_of_nonneg (by linarith)]
        field_simp [hε.ne']
        nlinarith [Real.rpow_nonneg hX0.le a]
  have horizontalBound (t : ℝ) (ht' : |t| = T) :
      ‖HIntegral (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X) a b t‖ ≤
      (16 * M) * Q * X ^ b / (ε * (1 + T ^ 2)) := by
    rw [HIntegral]
    calc
      _ ≤ ((2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        exact horizontalPoint σ t hσ.1.le hσ.2 ht'
      _ ≤ (16 * M) * Q * X ^ b / (ε * (1 + T ^ 2)) := by
        have hlen : |b - a| ≤ 2 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hab)]
          dsimp only [a, b, dirichletLTwistedSmoothedQuadraticConditionalLeft,
            dirichletLTwistedSmoothedQuadraticConditionalRight,
            dirichletLTwistedSmoothedQuadraticConditionalDelta]
          linarith
        have hden : 0 < ε * (1 + T ^ 2) := by positivity
        calc
          _ ≤ ((2 * Q) * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * 2 := by
            gcongr
          _ ≤ (16 * M) * Q * X ^ b / (ε * (1 + T ^ 2)) := by
            field_simp [hden.ne']
            nlinarith [Real.rpow_nonneg hX0.le b]
  exact ⟨hvertical,
    horizontalBound T (by simp [abs_of_nonneg hT0.le]),
    horizontalBound (-T) (by rw [abs_neg, abs_of_nonneg hT0.le])⟩

end AnalyticNumberTheory.LargeSieve