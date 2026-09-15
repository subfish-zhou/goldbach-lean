import MathlibNt.AnalyticNumberTheory.LargeSieve.ZetaPolePlusLogBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrincipalEulerCorrectionLogBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticValueAtOnePositive
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogDerivativeBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDifferenceBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds

/-!
# Closed quadratic zero-free ingredients

The endpoint optimization is intentionally not asserted here.  These public
lemmas close the vertical fundamental theorem, the low-height two-segment
argument once its sharp derivative budgets have been instantiated, and the
high-height `(3,4,1)` contradiction while consuming the actual principal
Euler-correction and pole-plus-log zeta bounds.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

variable {q : ℕ} [NeZero q]

/-- Genuine vertical fundamental theorem for a nonprincipal Dirichlet
`L`-function.  The derivative here is the real derivative of the actual
vertical restriction, so the statement contains no assumed path identity. -/
theorem integral_verticalDeriv_LFunction_eq_sub
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ)
    (hderivContinuous : Continuous
      (deriv (fun v : ℝ => χ.LFunction (1 + v * I)))) :
    (∫ u in (0 : ℝ)..t, deriv (fun v : ℝ => χ.LFunction (1 + v * I)) u) =
      χ.LFunction (1 + t * I) - χ.LFunction 1 := by
  let f : ℝ → ℂ := fun u => χ.LFunction (1 + u * I)
  have hdiff : ∀ u : ℝ, DifferentiableAt ℝ f u := by
    intro u
    exact (χ.differentiable_LFunction hχ (1 + u * I)).restrictScalars ℝ |>.comp u
      (differentiableAt_const (c := (1 : ℂ)).add
        ((differentiableAt_id.ofReal_comp).mul_const I))
  have hcont : Continuous (deriv f) := by simpa only [f] using hderivContinuous
  simpa only [f, ofReal_zero, zero_mul, add_zero] using
    (intervalIntegral.integral_deriv_eq_sub' (a := (0 : ℝ)) (b := t) f rfl
      (fun u _ => hdiff u) hcont.continuousOn)

/-- Integrating the conductor-height derivative estimate along a horizontal
segment gives a logarithmic, rather than polynomial-in-the-conductor, budget. -/
theorem norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ₁ σ₂ t : ℝ}
    (hσ₁half : 1 / 2 ≤ σ₁)
    (hσ₁lower :
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ₁)
    (hσ₁σ₂ : σ₁ ≤ σ₂) (hσ₂upper : σ₂ ≤ 2) :
    ‖χ.LFunction (σ₂ + t * I) - χ.LFunction (σ₁ + t * I)‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
        (σ₂ - σ₁) := by
  rw [← DirichletLWeakStripDifferenceBound.integral_deriv_LFunction_eq_sub
    χ hχ σ₁ σ₂ t]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr
    rw [_root_.abs_of_nonneg (sub_nonneg.mpr hσ₁σ₂)]
  · intro σ hσ
    rw [uIoc_of_le hσ₁σ₂, mem_Ioc] at hσ
    convert norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
      χ hχ (hσ₁half.trans hσ.1.le) (hσ.2.trans hσ₂upper)
      (hσ₁lower.trans hσ.1.le) using 1; ring

/-- Common conductor-height and zeta-pole scale used in the conditional
quadratic zero-free headline. -/
noncomputable def dirichletLQuadraticConditionalPowerZeroFreeH
    (q : ℕ) (t : ℝ) : ℝ :=
  1 + Real.log (dirichletLConductorHeightCutoff q t) +
    if _ht : t = 0 then 0
    else 1 + Real.log (|2 * t| + 2) + 1 / |2 * t|

/-- Integrating the global conductor-log derivative bound along the genuine
vertical segment gives a linear-in-`|t|` budget at `re s = 1`. -/
theorem norm_LFunction_vertical_sub_le_sixtyfour_mul_conductorHeightLogSq
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := by
  let C : ℝ := 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2
  have hmain : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
      C * ‖(1 + t * I : ℂ) - 1‖ :=
    (convex_segment (𝕜 := ℝ) (1 : ℂ) (1 + t * I)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℂ) (f := χ.LFunction) (C := C)
      (fun z _ => χ.differentiable_LFunction hχ z) (fun z hz => by
        rw [segment_eq_image_lineMap] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        have hu0 : 0 ≤ u := hu.1
        have hu1 : u ≤ 1 := hu.2
        have hline : AffineMap.lineMap (1 : ℂ) (1 + t * I) u = 1 + (u * t) * I := by
          apply Complex.ext <;> simp [AffineMap.lineMap_apply]
        have him : |(AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im| ≤ |t| := by
          rw [hline]
          simp only [add_im, one_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re,
            I_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
          rw [sub_zero, abs_mul, abs_of_nonneg hu0]
          exact mul_le_of_le_one_left (abs_nonneg t) hu1
        have hcut : dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im ≤
            dirichletLConductorHeightCutoff q t := by
          unfold dirichletLConductorHeightCutoff dirichletLHeightBlock
          exact Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.floor_mono him) 1)
        have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im := by
          exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
        have hcutR : (dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im : ℝ) ≤
            dirichletLConductorHeightCutoff q t := by exact_mod_cast hcut
        have hlog : Real.log (dirichletLConductorHeightCutoff q
            (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im) ≤
            Real.log (dirichletLConductorHeightCutoff q t) :=
          Real.log_le_log hcutpos hcutR
        have hd := norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
          χ hχ (σ := (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re)
            (t := (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im)
            (by rw [hline]; norm_num) (by rw [hline]; norm_num)
            (by
              have hp := log_conductorHeightCutoff_pos χ hχ
                (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im
              rw [show (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re = 1 by
                rw [hline]; simp]
              exact sub_le_self 1 (one_div_nonneg.mpr hp.le))
        rw [show (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).re +
            I * (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im =
            AffineMap.lineMap (1 : ℂ) (1 + t * I) u by
              rw [mul_comm I]; exact Complex.re_add_im _] at hd
        dsimp only [C]
        calc
          ‖fderiv ℂ χ.LFunction (AffineMap.lineMap (1 : ℂ) (1 + t * I) u)‖ ≤
              64 * (1 + Real.log (dirichletLConductorHeightCutoff q
                (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im)) ^ 2 := by
                  rw [← norm_deriv_eq_norm_fderiv]
                  exact hd
          _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            have hp := log_conductorHeightCutoff_pos χ hχ
              (AffineMap.lineMap (1 : ℂ) (1 + t * I) u).im
            exact pow_le_pow_left₀ (by linarith [hp]) (by linarith [hlog]) 2)
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hnorm : ‖(1 + t * I : ℂ) - 1‖ = |t| := by
    rw [show (1 + t * I : ℂ) - 1 = t * I by ring, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs]
  simpa only [C, hnorm] using hmain

/-- Low-height two-segment exclusion.  The endpoint value is identified with
its positive real part using quadraticity.  `hhorizontal` and `hvertical` are
the two sharp derivative-integral budgets, and the preceding theorem supplies
the required vertical fundamental theorem when establishing `hvertical`. -/
theorem LFunction_ne_zero_lowHeight_of_twoSegmentBudgets
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {β t Bh Bv : ℝ}
    (hhorizontal :
      ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤ Bh)
    (hvertical : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤ Bv)
    (hbudget : Bh + Bv < (χ.LFunction 1).re) :
    χ.LFunction (β + I * t) ≠ 0 := by
  intro hz
  have hz' : χ.LFunction (β + t * I) = 0 := by convert hz using 1; ring
  have hre := DirichletCharacter.LFunction_apply_one_re_pos_of_sq_eq_one hquad hχ
  have him := DirichletCharacter.LFunction_apply_one_im_eq_zero_of_sq_eq_one hquad hχ
  have hnormone : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [Complex.norm_def, Complex.normSq_apply, him]
    simp only [mul_zero, add_zero]
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_pos hre]
  have htri : ‖χ.LFunction 1‖ ≤
      ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ +
        ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ := by
    rw [hz', sub_zero]
    calc
      ‖χ.LFunction 1‖ = ‖χ.LFunction 1 - χ.LFunction (1 + t * I) +
          χ.LFunction (1 + t * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖χ.LFunction 1 - χ.LFunction (1 + t * I)‖ +
          ‖χ.LFunction (1 + t * I)‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  rw [hnormone] at htri
  linarith

/-- Actual principal-square estimate used in the high-height branch.  This
directly consumes both accepted analytic inputs; it is not an abstract source
predicate. -/
theorem norm_quadraticSquare_LFunction_le_principalPolePlusLog
    (Z : ℝ)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    {x t : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0) :
    ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ ≤
      (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) := by
  have hu : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have he := DirichletCharacter.norm_LFunction_sq_le_one_add_log_mul_riemannZeta
    χ hquad (s := 1 + x + I * (2 * t)) (by simp; linarith) (by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
      exact ht hh)
  calc
    _ ≤ (1 + Real.log q) * ‖riemannZeta (1 + x + I * (2 * t))‖ := he
    _ ≤ (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) := by
      gcongr
      simpa only [ofReal_mul, ofReal_ofNat] using hzeta x (2 * t) hx hx1 hu

/-- High-height `(3,4,1)` contradiction.  The actual principal-square bound is
invoked in the proof.  `htriv` and `hright` are precisely the elementary
principal-pole and Taylor estimates to be discharged by the surrounding
power-width arithmetic. -/
theorem LFunction_ne_zero_highHeight_of_valueProduct
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (_hχ : χ ≠ 1)
    {β t x D : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ht : t ≠ 0)
    (htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x)
    (hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ D * x)
    (hpay : 8 * (1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) * (D * x) ^ 4 < x ^ 3) :
    χ.LFunction (β + I * t) ≠ 0 := by
  have hsquare := norm_quadraticSquare_LFunction_le_principalPolePlusLog
    Z hzeta χ hquad hx hx1 ht
  have hp := χ.norm_LFunction_product_ge_one hx t
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
      simpa only [norm_mul, norm_pow] using hp) using 1; ring
  have hmajor : 1 ≤ (2 / x) ^ 3 * (D * x) ^ 4 *
      ((1 + Real.log q) *
        (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|))) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ _ := by gcongr
  have hm := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hx.le 3)
  have hcontr : x ^ 3 ≤ 8 * (1 + Real.log q) *
      (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)) * (D * x) ^ 4 := by
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * ((2 / x) ^ 3 * (D * x) ^ 4 *
          ((1 + Real.log q) *
            (Z * (1 + Real.log (|2 * t| + 2) + 1 / |2 * t|)))) := hm
      _ = _ := by field_simp [ne_of_gt hx]; ring
  exact False.elim ((not_lt_of_ge hcontr) hpay)

/-- The combined conductor-height/pole scale is at least one. -/
theorem one_le_dirichletLQuadraticConditionalPowerZeroFreeH
    (q : ℕ) [NeZero q] (t : ℝ) :
    1 ≤ dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  have hcut : (1 : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.mul_ne_zero (NeZero.ne q) (by simp [dirichletLHeightBlock]))
  have hlog : 0 ≤ Real.log (dirichletLConductorHeightCutoff q t) :=
    Real.log_nonneg hcut
  by_cases ht : t = 0
  · subst t
    simpa [dirichletLQuadraticConditionalPowerZeroFreeH] using
      (show (1 : ℝ) ≤ 1 + Real.log (dirichletLConductorHeightCutoff q 0) by linarith)
  · have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    have hinv : 0 < 1 / |2 * t| := one_div_pos.mpr habs
    simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
    linarith

/-- The conductor logarithm is dominated by the common scale. -/
theorem one_add_log_conductorHeightCutoff_le_quadraticH
    (q : ℕ) [NeZero q] (t : ℝ) :
    1 + Real.log (dirichletLConductorHeightCutoff q t) ≤
      dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  by_cases ht : t = 0
  · simp [dirichletLQuadraticConditionalPowerZeroFreeH, ht]
  · have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
    have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
    have hinv : 0 < 1 / |2 * t| := one_div_pos.mpr habs
    simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
    linarith

/-- For nonzero height, the pole-plus-log factor is also dominated by the
common scale. -/
theorem one_add_log_twoHeight_add_inv_le_quadraticH
    (q : ℕ) [NeZero q] {t : ℝ} (ht : t ≠ 0) :
    1 + Real.log (|2 * t| + 2) + 1 / |2 * t| ≤
      dirichletLQuadraticConditionalPowerZeroFreeH q t := by
  have hcut : (1 : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.mul_ne_zero (NeZero.ne q) (by simp [dirichletLHeightBlock]))
  have hlog : 0 ≤ Real.log (dirichletLConductorHeightCutoff q t) :=
    Real.log_nonneg hcut
  simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht]
  linarith

/-- A genuine conditional quadratic headline.  A Siegel-type lower bound at
one, with its premise left explicit, gives a single power-width zero-free
region at every height.  The low branch uses both the horizontal and the
accepted vertical derivative budgets; the complementary branch uses the
`(3,4,1)` value-product argument. -/
theorem exists_dirichletL_quadratic_conditional_powerZeroFree
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β t : ℝ),
        χ ^ 2 = 1 → χ ≠ 1 →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re →
        β ∈ Set.Ico
          (1 - A * (q : ℝ) ^ (-2 * η) /
            (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
        χ.LFunction (β + I * t) ≠ 0 := by
  obtain ⟨Z, hZ, hzeta⟩ := zeta_pole_plus_log_bound
  let A : ℝ := min (1 / 2) (min (c / 256) (1 / (16 * Z * 128 ^ 4)))
  have hA : 0 < A := by
    dsimp only [A]
    exact lt_min (by norm_num) (lt_min (div_pos hc (by norm_num)) (by positivity))
  refine ⟨A, hA, ?_⟩
  intro q _ χ β t hquad hχ hSiegel hβ
  let H : ℝ := dirichletLQuadraticConditionalPowerZeroFreeH q t
  let p : ℝ := (q : ℝ) ^ (-2 * η)
  let r : ℝ := (q : ℝ) ^ (-η)
  let x : ℝ := A * p / H ^ 12
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hH1 : 1 ≤ H := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q t
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hp : 0 < p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hr : 0 < r := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hq1) _
  have hpr : p ≤ r := by
    dsimp only [p, r]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : -2 * η ≤ 0)
  have hHpow : 1 ≤ H ^ 12 := one_le_pow₀ hH1
  have hx : 0 < x := div_pos (mul_pos hA hp) (pow_pos hH 12)
  have hAhalf : A ≤ 1 / 2 := by exact min_le_left _ _
  have hA1 : A ≤ 1 := hAhalf.trans (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    exact (div_le_one (pow_pos hH 12)).2
      (((mul_le_of_le_one_right hA.le hp1).trans hA1).trans hHpow)
  have hβleft : 1 - x ≤ β := by simpa only [x, p, H] using hβ.1
  have hβhalf : 1 / 2 ≤ β := by
    have hxhalf : x ≤ 1 / 2 := by
      have hsmall : A ≤ 1 / 2 := hAhalf
      dsimp only [x]
      calc
        A * p / H ^ 12 ≤ A := by
          rw [div_le_iff₀ (pow_pos hH 12)]
          nlinarith [hHpow, mul_le_of_le_one_right hA.le hp1]
        _ ≤ 1 / 2 := hsmall
    linarith
  -- Both height branches use the same conductor-log strip condition.
  have hnear :
      1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    have hlogpos := log_conductorHeightCutoff_pos χ hχ t
    have hone : x ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) := by
      have hlogle : Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
        have := one_add_log_conductorHeightCutoff_le_quadraticH q t
        linarith
      apply (le_div_iff₀ hlogpos).2
      calc
        x * Real.log (dirichletLConductorHeightCutoff q t) ≤ x * H :=
          mul_le_mul_of_nonneg_left hlogle hx.le
        _ ≤ 1 := by
          dsimp only [x]
          rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hH 12)]
          nlinarith [hHpow, one_le_pow₀ hH1 (n := 11),
            mul_le_of_le_one_right hA.le hp1]
    linarith
  have hlogH := one_add_log_conductorHeightCutoff_le_quadraticH q t
  by_cases htlow : |t| ≤ x
  · have hhorizontal := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
      χ hχ hβhalf hnear hβ.2.le (by norm_num : (1 : ℝ) ≤ 2)
    have hvertical :=
      norm_LFunction_vertical_sub_le_sixtyfour_mul_conductorHeightLogSq χ hχ t
    have hBh : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤
        64 * H ^ 2 * x := by
      calc
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
            (1 - β) := by simpa using hhorizontal
        _ ≤ 64 * H ^ 2 * x := by
          have hwidth : 1 - β ≤ x := by linarith
          have hnonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ.2.le
          gcongr
    have hBv : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤
        64 * H ^ 2 * x := by
      calc
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| :=
          hvertical
        _ ≤ 64 * H ^ 2 * x := by
          gcongr
    have hAlow : A ≤ c / 256 :=
      (min_le_right (1 / 2) _).trans (min_le_left _ _)
    have hbudget : 64 * H ^ 2 * x + 64 * H ^ 2 * x < (χ.LFunction 1).re := by
      have hpow10 : 1 ≤ H ^ 10 := one_le_pow₀ hH1
      have hcalc : 128 * H ^ 2 * x ≤ (c / 2) * r := by
        dsimp only [x]
        have heq : 128 * H ^ 2 * (A * p / H ^ 12) = 128 * A * p / H ^ 10 := by
          field_simp [ne_of_gt hH]
        rw [heq, div_le_iff₀ (pow_pos hH 10)]
        have hAp : A * p ≤ (c / 256) * r :=
          mul_le_mul hAlow hpr hp.le (by positivity)
        have hscale : (c / 2) * r ≤ (c / 2) * r * H ^ 10 :=
          le_mul_of_one_le_right (by positivity) hpow10
        nlinarith
      have : (c / 2) * r < c * r :=
        mul_lt_mul_of_pos_right (by linarith) hr
      linarith
    exact LFunction_ne_zero_lowHeight_of_twoSegmentBudgets χ hquad hχ hBh hBv hbudget
  · have ht : t ≠ 0 := by
      intro h
      subst t
      simp only [abs_zero] at htlow
      exact htlow hx.le
    have hright0 := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
      χ hχ (σ₁ := β) (σ₂ := 1 + x) (t := t) hβhalf
      hnear
      (by linarith [hβ.2]) (by linarith [hx1] : 1 + x ≤ 2)
    have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
      rw [DirichletCharacter.LFunctionTrivChar]
      calc
        ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
          convert norm_dirichletLFunction_le
            (1 : DirichletCharacter ℂ q) (1 + x) 0 (by linarith) using 1 <;> norm_num
        _ ≤ 2 / x := by
          rw [le_div_iff₀ hx]
          field_simp [ne_of_gt hx]
          linarith
    intro hz
    have hz' : χ.LFunction (β + t * I) = 0 := by
      convert hz using 1; ring
    have hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ (128 * H ^ 2) * x := by
      calc
        ‖χ.LFunction (1 + x + I * t)‖ =
            ‖χ.LFunction (1 + x + t * I) - χ.LFunction (β + t * I)‖ := by
              rw [hz', sub_zero]
              congr 2
              ring
        _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
            ((1 + x) - β) := by
              convert hright0 using 1; push_cast; ring
        _ ≤ (128 * H ^ 2) * x := by
          have hwidth : 1 - β ≤ x := by linarith
          have hdiff : (1 + x) - β ≤ 2 * x := by linarith
          have hdiff0 : 0 ≤ (1 + x) - β := by linarith [hβ.2]
          have hlogH' :
              1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ H := by
            simpa only [H] using hlogH
          calc
            64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
                ((1 + x) - β) ≤ 64 * H ^ 2 * ((1 + x) - β) := by gcongr
            _ ≤ 64 * H ^ 2 * (2 * x) := by gcongr
            _ = (128 * H ^ 2) * x := by ring
    have hqcut : q ≤ dirichletLConductorHeightCutoff q t := by
      unfold dirichletLConductorHeightCutoff
      exact Nat.le_mul_of_pos_right q (by simp [dirichletLHeightBlock])
    have hlogq : 1 + Real.log q ≤ H := by
      have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
      have hcast : (q : ℝ) ≤ dirichletLConductorHeightCutoff q t := by
        exact_mod_cast hqcut
      have hl := Real.log_le_log hqpos hcast
      have hh := one_add_log_conductorHeightCutoff_le_quadraticH q t
      linarith
    let S : ℝ := 1 + Real.log (|2 * t| + 2) + 1 / |2 * t|
    have hSpos : 0 < S := by
      dsimp only [S]
      have habs : 0 < |2 * t| := abs_pos.mpr (mul_ne_zero (by norm_num) ht)
      have hlogtwo : 0 ≤ Real.log (|2 * t| + 2) :=
        Real.log_nonneg (by linarith [abs_nonneg (2 * t)])
      positivity
    have hSH : S ≤ H := by
      simpa only [S] using one_add_log_twoHeight_add_inv_le_quadraticH q ht
    have hmajor :
        8 * (1 + Real.log q) * (Z * S) * ((128 * H ^ 2) * x) ^ 4 ≤
          8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 := by
      gcongr
    have hAhigh : A ≤ 1 / (16 * Z * 128 ^ 4) :=
      (min_le_right (1 / 2) _).trans (min_le_right _ _)
    have hdenpos : 0 < 16 * Z * 128 ^ 4 := by positivity
    have hZA : 16 * Z * 128 ^ 4 * A ≤ 1 := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        (le_div_iff₀ hdenpos).mp hAhigh
    have hZAp : 16 * Z * 128 ^ 4 * A * p ≤ 1 :=
      (mul_le_of_le_one_right (by positivity) hp1).trans hZA
    have hfactor : 8 * Z * 128 ^ 4 * A * p / H ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (pow_pos hH 2)]
      have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hH1
      nlinarith
    have hid :
        8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 =
          (8 * Z * 128 ^ 4 * A * p / H ^ 2) * x ^ 3 := by
      dsimp only [x]
      field_simp [ne_of_gt hH]
    have hpay :
        8 * (1 + Real.log q) * (Z * S) * ((128 * H ^ 2) * x) ^ 4 < x ^ 3 := by
      calc
        _ ≤ 8 * H * (Z * H) * ((128 * H ^ 2) * x) ^ 4 := hmajor
        _ = (8 * Z * 128 ^ 4 * A * p / H ^ 2) * x ^ 3 := hid
        _ ≤ (1 / 2) * x ^ 3 := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hx.le 3)
        _ < x ^ 3 := by nlinarith [pow_pos hx 3]
    have hne := LFunction_ne_zero_highHeight_of_valueProduct Z hZ hzeta χ hquad hχ
      (β := β) (t := t) (x := x) (D := 128 * H ^ 2)
      hx hx1 ht htriv hright (by simpa only [S] using hpay)
    exact hne hz

end AnalyticNumberTheory.LargeSieve