import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalCrossZeroRectangle

/-!
# Quantitative logarithmic derivative in the quadratic central band

This file turns the raw lower bound at `s = 1` into an explicit lower bound
throughout the central band used by the cross-zero rectangle.  In particular,
the denominator in `L'/L` is paid quantitatively; zero-freeness or compactness
alone is never used as a substitute for a uniform lower bound.

The resulting bound retains the honest factor `q^η / c` forced by the supplied
raw Siegel lower bound `c q⁻η ≤ L(1,χ)`.  Removing that power requires a stronger
(polylogarithmic) lower input, not a topological argument.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

private theorem central_band_parameter_bounds
    {q : ℕ} [NeZero q] {A c η T : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T) :
    let H₀ := dirichletLQuadraticConditionalCentralH q T
    let H := dirichletLQuadraticConditionalFixedH q
      (dirichletLQuadraticConditionalCentralHeight c η q T) T
    let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
    1 ≤ H₀ ∧ H₀ ≤ H ∧ 0 < w ∧
      64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 ∧
      w ≤ 1 / H₀ := by
  dsimp only
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  let H₀ : ℝ := dirichletLQuadraticConditionalCentralH q T
  let τ : ℝ := dirichletLQuadraticConditionalCentralHeight c η q T
  let H : ℝ := dirichletLQuadraticConditionalFixedH q τ T
  let w : ℝ := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hH₀ : 1 ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_nonneg hcut]
  have hτ : 0 < τ := by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact lt_min hT (by positivity)
  have hH₀H : H₀ ≤ H := by
    dsimp only [H₀, H, dirichletLQuadraticConditionalCentralH,
      dirichletLQuadraticConditionalFixedH]
    have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
    have hinv : 0 < 1 / (2 * τ) := by positivity
    linarith
  have hH : 1 ≤ H := hH₀.trans hH₀H
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hpr : (q : ℝ) ^ (-2 * η) ≤ (q : ℝ) ^ (-η) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hw : 0 < w := by
    dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
    positivity
  have hHpow2 : H₀ ^ 2 ≤ H ^ 12 := by
    calc
      H₀ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hH₀) hH₀H 2
      _ ≤ H ^ 12 := pow_le_pow_right₀ hH (by omega)
  have hwpay : 64 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hwbudget : w ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      rw [div_le_div_iff₀ (pow_pos hHpos 12) (by positivity)]
      have hAp : A * (q : ℝ) ^ (-2 * η) ≤ (c / 256) * (q : ℝ) ^ (-η) :=
        mul_le_mul hAc hpr hp.le (by positivity)
      calc
        A * (q : ℝ) ^ (-2 * η) * (256 * H₀ ^ 2) ≤
            ((c / 256) * (q : ℝ) ^ (-η)) * (256 * H₀ ^ 2) := by gcongr
        _ = c * (q : ℝ) ^ (-η) * H₀ ^ 2 := by ring
        _ ≤ c * (q : ℝ) ^ (-η) * H ^ 12 := by gcongr
    have hmul : 256 * H₀ ^ 2 * w ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ (by positivity : 0 < 256 * H₀ ^ 2)).mp hwbudget
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * w = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * w) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hp1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hwH₀ : w * H₀ ≤ 1 := by
    dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
    rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hHpos 12)]
    calc
      A * (q : ℝ) ^ (-2 * η) * H₀ ≤ H₀ := by
        have hprod : A * (q : ℝ) ^ (-2 * η) ≤ 1 := by
          calc
            A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
              mul_le_mul hAhalf hp1 hp.le (by norm_num)
            _ ≤ 1 := by norm_num
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hprod (zero_le_one.trans hH₀)
      _ ≤ H ^ 12 := hH₀H.trans (by
        simpa only [pow_one] using (pow_le_pow_right₀ hH (by norm_num : 1 ≤ 12)))
      _ = 1 * H ^ 12 := by ring
  have hwInv : w ≤ 1 / H₀ := (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hH₀)).2
    (by simpa [mul_comm] using hwH₀)
  simpa only [H₀, H, w, τ] using ⟨hH₀, hH₀H, hw, hwpay, hwInv⟩

/-- Shared geometric conditions for applying the conductor-height derivative estimates. -/
private theorem central_band_point_bounds
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    1 / 2 ≤ β ∧
      1 + Real.log (dirichletLConductorHeightCutoff q t) ≤
        dirichletLQuadraticConditionalCentralH q T ∧
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_band_parameter_bounds (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  have htT : |t| ≤ T := ht.trans (by
    dsimp only [τ, dirichletLQuadraticConditionalCentralHeight]
    exact min_le_left _ _)
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) htT
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlog : 1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H₀ := by
    dsimp only [H₀, dirichletLQuadraticConditionalCentralH]
    linarith [Real.log_le_log hcutpos hcutR]
  have hβhalf : 1 / 2 ≤ β := by
    have hq1 : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hpq1 : (q : ℝ) ^ (-2 * η) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
    have Hge : 1 ≤ dirichletLQuadraticConditionalFixedH q τ T := hp.1.trans hp.2.1
    have hw_half : w ≤ 1 / 2 := by
      dsimp only [w, dirichletLQuadraticConditionalCrossZeroWidth]
      rw [div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one Hge) 12)]
      calc
        A * (q : ℝ) ^ (-2 * η) ≤ 1 / 2 := by
          calc
            A * (q : ℝ) ^ (-2 * η) ≤ (1 / 2 : ℝ) * 1 :=
              mul_le_mul hAhalf hpq1 (Real.rpow_nonneg (by positivity) _) (by norm_num)
            _ = 1 / 2 := by ring
        _ ≤ (1 / 2) * (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (one_le_pow₀ Hge) (by norm_num : (0 : ℝ) ≤ 1 / 2))
    dsimp only [w] at hw_half hβ
    linarith
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hwlog : w ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      apply (le_div_iff₀ hlogpos).2
      calc
        w * Real.log (dirichletLConductorHeightCutoff q t) ≤ w * H₀ := by
          exact mul_le_mul_of_nonneg_left (by linarith [hlog]) hp.2.2.1.le
        _ ≤ 1 := by
          exact (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hp.1)).mp hp.2.2.2.2
    dsimp only [w] at hwlog hβ
    linarith
  exact ⟨hβhalf, hlog, hnear⟩

/-- Quantitative central-band lower bound.  It is obtained by transporting the
raw lower bound at `1` along one vertical and one horizontal segment. -/
theorem norm_LFunction_ge_half_siegel_on_quadraticConditionalCentralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    c * (q : ℝ) ^ (-η) / 2 ≤ ‖χ.LFunction (β + I * t)‖ := by
  let H₀ := dirichletLQuadraticConditionalCentralH q T
  let τ := dirichletLQuadraticConditionalCentralHeight c η q T
  let w := dirichletLQuadraticConditionalCrossZeroWidth A c η q T
  have hp := central_band_parameter_bounds (q := q) hA hAc hAhalf hc hη hT
  dsimp only at hp
  obtain ⟨hβhalf, hlog, hnear⟩ :=
    central_band_point_bounds χ hχ hA hAc hAhalf hc hη hT hβ ht
  have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ hβhalf hnear hβone (by norm_num : (1 : ℝ) ≤ 2)
  have hvertical := norm_LFunction_vertical_sub_le_sixtyfour_mul_conductorHeightLogSq χ hχ t
  have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤
      64 * H₀ ^ 2 * w := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * (1 - β) := by
        simpa using hhorizontal
      _ ≤ 64 * H₀ ^ 2 * w := by
        have hwidth : 1 - β ≤ w := by dsimp only [w] at hβ ⊢; linarith
        gcongr
  have hτpay : 64 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) / 4 := by
    have hτbound : τ ≤ c * (q : ℝ) ^ (-η) / (256 * H₀ ^ 2) := by
      dsimp only [τ, H₀, dirichletLQuadraticConditionalCentralHeight]
      exact min_le_right _ _
    have hH₀pos : 0 < H₀ := lt_of_lt_of_le zero_lt_one hp.1
    have hmul : 256 * H₀ ^ 2 * τ ≤ c * (q : ℝ) ^ (-η) := by
      have hx := (le_div_iff₀ (by positivity : 0 < 256 * H₀ ^ 2)).mp hτbound
      simpa only [mul_comm] using hx
    calc
      64 * H₀ ^ 2 * τ = (1 / 4 : ℝ) * (256 * H₀ ^ 2 * τ) := by ring
      _ ≤ (1 / 4 : ℝ) * (c * (q : ℝ) ^ (-η)) := by gcongr
      _ = c * (q : ℝ) ^ (-η) / 4 := by ring
  have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      c * (q : ℝ) ^ (-η) / 4 := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := hvertical
      _ ≤ 64 * H₀ ^ 2 * τ := by gcongr
      _ ≤ _ := hτpay
  have hclose : ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ ≤
      c * (q : ℝ) ^ (-η) / 2 := by
    calc
      _ ≤ ‖χ.LFunction (β + I * t) - χ.LFunction (1 + I * t)‖ +
          ‖χ.LFunction (1 + I * t) - χ.LFunction 1‖ := by
            simpa only [sub_add_sub_cancel] using norm_add_le
              (χ.LFunction (β + I * t) - χ.LFunction (1 + I * t))
              (χ.LFunction (1 + I * t) - χ.LFunction 1)
      _ ≤ 64 * H₀ ^ 2 * w + c * (q : ℝ) ^ (-η) / 4 := by
        gcongr
        · rw [norm_sub_rev]
          simpa [mul_comm] using hBh
        · simpa [mul_comm] using hBv
      _ ≤ c * (q : ℝ) ^ (-η) / 2 := by linarith [hp.2.2.2.1]
  have hLone : c * (q : ℝ) ^ (-η) ≤ ‖χ.LFunction 1‖ :=
    hSiegel.trans (Complex.re_le_norm _)
  calc
    c * (q : ℝ) ^ (-η) / 2
        ≤ ‖χ.LFunction 1‖ - ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ := by linarith
    _ ≤ ‖χ.LFunction (β + I * t)‖ := by
      have htri := norm_add_le
        (χ.LFunction 1 - χ.LFunction (β + I * t)) (χ.LFunction (β + I * t))
      rw [sub_add_cancel] at htri
      have hrev : ‖χ.LFunction 1 - χ.LFunction (β + I * t)‖ =
          ‖χ.LFunction (β + I * t) - χ.LFunction 1‖ := norm_sub_rev _ _
      rw [hrev] at htri
      linarith

/-- Explicit `L'/L` bound on the central band.  The only inverse lower-bound
factor is the visible `2 / (c q⁻η)`. -/
theorem norm_logDerivative_le_on_quadraticConditionalCentralBand
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A c η T β t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hβ : 1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ β)
    (hβone : β ≤ 1)
    (ht : |t| ≤ dirichletLQuadraticConditionalCentralHeight c η q T) :
    ‖deriv χ.LFunction (β + I * t) / χ.LFunction (β + I * t)‖ ≤
      (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
        (c * (q : ℝ) ^ (-η)) := by
  have hlower := norm_LFunction_ge_half_siegel_on_quadraticConditionalCentralBand
    χ hχ hA hAc hAhalf hc hη hT hSiegel hβ hβone ht
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hden : 0 < c * (q : ℝ) ^ (-η) := mul_pos hc (Real.rpow_pos_of_pos hq _)
  obtain ⟨hβhalf, hlog, hnear⟩ :=
    central_band_point_bounds χ hχ hA hAc hAhalf hc hη hT hβ ht
  have hderiv := norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
    χ hχ hβhalf (by linarith) hnear
  rw [norm_div]
  calc
    ‖deriv χ.LFunction (β + I * t)‖ / ‖χ.LFunction (β + I * t)‖
        ≤ ‖deriv χ.LFunction (β + I * t)‖ /
            (c * (q : ℝ) ^ (-η) / 2) := by
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hlower
    _ ≤ (64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2) /
            (c * (q : ℝ) ^ (-η) / 2) := by
          exact div_le_div_of_nonneg_right hderiv (by positivity)
    _ ≤ (64 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
            (c * (q : ℝ) ^ (-η) / 2) := by
          gcongr
    _ = (128 * (dirichletLQuadraticConditionalCentralH q T) ^ 2) /
            (c * (q : ℝ) ^ (-η)) := by field_simp; ring

end AnalyticNumberTheory.LargeSieve
