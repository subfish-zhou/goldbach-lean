import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalPowerZeroFree
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLNonquadraticConductorLogRectangle

/-!
# Fixed-height quadratic rectangles away from height zero

The power-width quadratic headline contains the term `1 / |2t|`.  Consequently
it does not by itself contain a positive-width rectangle crossing `t = 0`.
This file extracts the strongest literal rectangular consequence: two closed
rectangles at heights `τ ≤ |t| ≤ T`.  It also records the quantitative
derivative and logarithmic-derivative estimates available there.  The latter
keeps the actual L-value in the denominator; no lower bound for that value is
silently postulated.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound

/-- A uniform majorant for the height-dependent scale on `τ ≤ |t| ≤ T`. -/
noncomputable def dirichletLQuadraticConditionalFixedH
    (q : ℕ) (τ T : ℝ) : ℝ :=
  1 + Real.log (dirichletLNonquadraticConductorLogCutoff q T) +
    (1 + Real.log (2 * T + 2) + 1 / (2 * τ))

/-- The fixed left edge obtained from a power-width headline on an annulus of
heights. -/
noncomputable def dirichletLQuadraticConditionalFixedLeft
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : ℝ :=
  1 - A * (q : ℝ) ^ (-2 * η) /
    (dirichletLQuadraticConditionalFixedH q τ T) ^ 12

/-- The upper fixed rectangle, with heights from `τ` to `T`. -/
def dirichletLQuadraticConditionalUpperRectangle
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : Set ℂ :=
  ((dirichletLQuadraticConditionalFixedLeft A η q τ T : ℂ) + I * τ).Rectangle
    (2 + I * T)

/-- The lower fixed rectangle, with heights from `-T` to `-τ`. -/
def dirichletLQuadraticConditionalLowerRectangle
    (A η : ℝ) (q : ℕ) (τ T : ℝ) : Set ℂ :=
  ((dirichletLQuadraticConditionalFixedLeft A η q τ T : ℂ) - I * T).Rectangle
    (2 - I * τ)

/-- On a closed height annulus, the singular height scale has a genuine fixed
majorant. -/
theorem dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH
    {q : ℕ} [NeZero q] {τ T t : ℝ}
    (hτ : 0 < τ) (hT : τ ≤ T) (htlow : τ ≤ |t|) (hthigh : |t| ≤ T) :
    dirichletLQuadraticConditionalPowerZeroFreeH q t ≤
      dirichletLQuadraticConditionalFixedH q τ T := by
  have ht : t ≠ 0 := by
    intro ht
    subst t
    simp only [abs_zero] at htlow
    linarith
  have hcut := dirichletLConductorHeightCutoff_le_fixedHeightCutoff (q := q) hthigh
  have hcutpos : (0 : ℝ) < dirichletLConductorHeightCutoff q t := by
    exact_mod_cast Nat.mul_pos (NeZero.pos q) (by simp [dirichletLHeightBlock])
  have hcutR : (dirichletLConductorHeightCutoff q t : ℝ) ≤
      dirichletLNonquadraticConductorLogCutoff q T := by exact_mod_cast hcut
  have hlogcut := Real.log_le_log hcutpos hcutR
  have habs : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : |2 * t| + 2 ≤ 2 * T + 2 := by rw [habs]; linarith
  have hargpos : 0 < |2 * t| + 2 := by linarith [abs_nonneg (2 * t)]
  have hlogarg := Real.log_le_log hargpos harg
  have hden : 0 < 2 * τ := by positivity
  have habsden : 2 * τ ≤ |2 * t| := by rw [habs]; linarith
  have hinv : 1 / |2 * t| ≤ 1 / (2 * τ) :=
    one_div_le_one_div_of_le hden habsden
  simp only [dirichletLQuadraticConditionalPowerZeroFreeH, dif_neg ht,
    dirichletLQuadraticConditionalFixedH]
  linarith

private theorem quadratic_fixed_parameters
    {q : ℕ} [NeZero q] {A η τ T : ℝ}
    (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T) :
    0 < dirichletLQuadraticConditionalFixedH q τ T ∧
      dirichletLQuadraticConditionalFixedLeft A η q τ T < 1 ∧
      dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hcut : (1 : ℝ) ≤ dirichletLNonquadraticConductorLogCutoff q T := by
    exact_mod_cast (show 1 ≤ dirichletLNonquadraticConductorLogCutoff q T by
      unfold dirichletLNonquadraticConductorLogCutoff
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne q) (by
        unfold dirichletLNonquadraticConductorLogHeightBlock
        omega)))
  have hlogcut : 0 ≤ Real.log (dirichletLNonquadraticConductorLogCutoff q T : ℝ) :=
    Real.log_nonneg hcut
  have hT0 : 0 < T := lt_of_lt_of_le hτ hT
  have hlogarg : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith)
  have hH : 0 < dirichletLQuadraticConditionalFixedH q τ T := by
    dsimp only [dirichletLQuadraticConditionalFixedH]
    positivity
  have hp : 0 < (q : ℝ) ^ (-2 * η) := Real.rpow_pos_of_pos hq _
  have hw : 0 < A * (q : ℝ) ^ (-2 * η) /
      (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by positivity
  refine ⟨hH, ?_, ?_⟩
  · dsimp only [dirichletLQuadraticConditionalFixedLeft]
    linarith
  · dsimp only [dirichletLQuadraticConditionalFixedLeft]
    linarith

private theorem LFunction_ne_zero_on_quadraticConditionalRectangle_aux
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0)
    {s : ℂ} (hre : dirichletLQuadraticConditionalFixedLeft A η q τ T ≤ s.re)
    (hre2 : s.re ≤ 2) (htlow : τ ≤ |s.im|) (hthigh : |s.im| ≤ T) :
    χ.LFunction s ≠ 0 := by
  by_cases hsre : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hsre
  · have hsrelt : s.re < 1 := lt_of_not_ge hsre
    have hHF := dirichletLQuadraticConditionalPowerZeroFreeH_le_fixedH (q := q)
      hτ hT htlow hthigh
    have hHlocal := one_le_dirichletLQuadraticConditionalPowerZeroFreeH q s.im
    have hHfixed : 0 < dirichletLQuadraticConditionalFixedH q τ T :=
      (quadratic_fixed_parameters (q := q) (η := η) hA hτ hT).1
    have hp : 0 ≤ A * (q : ℝ) ^ (-2 * η) := by positivity
    have hpow : (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12 ≤
        (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 := by
      exact pow_le_pow_left₀ (zero_le_one.trans hHlocal) hHF 12
    have hwidth : A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalFixedH q τ T) ^ 12 ≤
        A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12 := by
      exact div_le_div_of_nonneg_left hp (pow_pos (by linarith) 12) hpow
    have hβ : s.re ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q s.im) ^ 12) 1 := by
      refine ⟨?_, hsrelt⟩
      dsimp only [dirichletLQuadraticConditionalFixedLeft] at hre
      linarith
    have hz := hzero s.re s.im hβ
    have hsrepr : ((s.re : ℂ) + I * s.im) = s := by
      apply Complex.ext <;> simp
    simpa only [hsrepr] using hz

/-- The all-height power-width hypothesis gives zero-freeness on the upper
fixed rectangle. -/
theorem LFunction_ne_zero_on_quadraticConditionalUpperRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0) :
    ∀ s ∈ dirichletLQuadraticConditionalUpperRectangle A η q τ T,
      χ.LFunction s ≠ 0 := by
  intro s hs
  rw [dirichletLQuadraticConditionalUpperRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  have hp := quadratic_fixed_parameters (q := q) (η := η) hA hτ hT
  rw [Set.uIcc_of_le hp.2.2, Set.uIcc_of_le hT] at hs
  apply LFunction_ne_zero_on_quadraticConditionalRectangle_aux (q := q) χ hχ hA hτ hT hzero
    hs.1.1 hs.1.2
  · rw [abs_of_nonneg (hτ.le.trans hs.2.1)]
    exact hs.2.1
  · rw [abs_of_nonneg (hτ.le.trans hs.2.1)]
    exact hs.2.2

/-- The analogous lower fixed rectangle is zero-free. -/
theorem LFunction_ne_zero_on_quadraticConditionalLowerRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0) :
    ∀ s ∈ dirichletLQuadraticConditionalLowerRectangle A η q τ T,
      χ.LFunction s ≠ 0 := by
  intro s hs
  rw [dirichletLQuadraticConditionalLowerRectangle, Complex.Rectangle,
    Complex.mem_reProdIm] at hs
  norm_num at hs
  have hp := quadratic_fixed_parameters (q := q) (η := η) hA hτ hT
  rw [Set.uIcc_of_le hp.2.2, Set.uIcc_of_le (by linarith : -T ≤ -τ)] at hs
  rcases hs with ⟨⟨hreL, hreR⟩, ⟨himL, himR⟩⟩
  have him_nonpos : s.im ≤ 0 := by linarith
  have habsim : |s.im| = -s.im := abs_of_nonpos him_nonpos
  apply LFunction_ne_zero_on_quadraticConditionalRectangle_aux (q := q) χ hχ hA hτ hT hzero
    hreL hreR
  · rw [habsim]
    linarith
  · rw [habsim]
    linarith

/-- The logarithmic derivative is holomorphic on the upper fixed rectangle. -/
theorem logDerivative_holomorphicOn_quadraticConditionalUpperRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {A η τ T : ℝ} (hA : 0 < A) (hτ : 0 < τ) (hT : τ ≤ T)
    (hzero : ∀ (β t : ℝ),
      β ∈ Ico
        (1 - A * (q : ℝ) ^ (-2 * η) /
          (dirichletLQuadraticConditionalPowerZeroFreeH q t) ^ 12) 1 →
      χ.LFunction (β + I * t) ≠ 0) :
    HolomorphicOn (fun s => deriv χ.LFunction s / χ.LFunction s)
      (dirichletLQuadraticConditionalUpperRectangle A η q τ T) := by
  have hL : Differentiable ℂ χ.LFunction := χ.differentiable_LFunction hχ
  exact hL.deriv.differentiableOn.div hL.differentiableOn
    (LFunction_ne_zero_on_quadraticConditionalUpperRectangle χ hχ hA hτ hT hzero)

/-- Explicit quantitative bound supplied by the production derivative theorem.
Unlike a fictitious uniform lower bound, this statement displays the exact
remaining denominator. -/
theorem norm_logDerivative_le_derivativeBudget_div_LValue
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ t : ℝ} (hσhalf : 1 / 2 ≤ σ) (hσtwo : σ ≤ 2)
    (hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ σ) :
    ‖deriv χ.LFunction (σ + I * t) / χ.LFunction (σ + I * t)‖ ≤
      (64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2) /
        ‖χ.LFunction (σ + I * t)‖ := by
  rw [norm_div]
  exact div_le_div_of_nonneg_right
    (norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
      χ hχ hσhalf hσtwo hnear) (norm_nonneg _)

end AnalyticNumberTheory.LargeSieve