import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogValueBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalConductorLogDerivativeBound
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripDifferenceBound

/-!
# A conductor-logarithmic global nonquadratic zero-free region

The de la Vallée Poussin product lower bound is combined directly with the
natural-order conductor-height value and derivative estimates.  In particular,
the resulting width contains no positive power of the modulus.
-/

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound
open DirichletLWeakStripDifferenceBound

/-- Doubling the height at most doubles the integral height block. -/
lemma dirichletLHeightBlock_two_mul_le (t : ℝ) :
    dirichletLHeightBlock (2 * t) ≤ 2 * dirichletLHeightBlock t := by
  have hfloor : (⌊|2 * t|⌋₊ : ℝ) ≤ |2 * t| := Nat.floor_le (abs_nonneg _)
  have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
  have ht := abs_lt_heightBlock t
  have hltR : (⌊|2 * t|⌋₊ : ℝ) < 2 * dirichletLHeightBlock t := by
    calc
      (⌊|2 * t|⌋₊ : ℝ) ≤ |2 * t| := hfloor
      _ = 2 * |t| := habs
      _ < 2 * dirichletLHeightBlock t := by nlinarith
  have hltN : ⌊|2 * t|⌋₊ < 2 * dirichletLHeightBlock t := by exact_mod_cast hltR
  simpa only [dirichletLHeightBlock] using (Nat.add_one_le_iff.mpr hltN)

/-- The cutoff at doubled height is bounded by the square of the original
cutoff once the character is nonprincipal. -/
lemma dirichletLConductorHeightCutoff_two_mul_le_sq
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    dirichletLConductorHeightCutoff q (2 * t) ≤
      (dirichletLConductorHeightCutoff q t) ^ 2 := by
  let m := dirichletLConductorHeightCutoff q t
  have hm : 2 ≤ m := two_le_conductorHeightCutoff χ hχ t
  have hblock := dirichletLHeightBlock_two_mul_le t
  have htwo : dirichletLConductorHeightCutoff q (2 * t) ≤ 2 * m := by
    dsimp only [m, dirichletLConductorHeightCutoff]
    nlinarith [Nat.mul_le_mul_left q hblock]
  calc
    dirichletLConductorHeightCutoff q (2 * t) ≤ 2 * m := htwo
    _ ≤ m ^ 2 := by nlinarith

/-- A nonquadratic character has no zero in a purely conductor-logarithmic
left neighbourhood of one. -/
theorem norm_LFunction_ne_zero_of_nonquadratic_conductorLog
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    {β t : ℝ}
    (hβ : β ∈ Set.Ico
      (1 - 1 / (274877906944 *
        (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) 1) :
    χ.LFunction (β + I * t) ≠ 0 := by
  let m : ℕ := dirichletLConductorHeightCutoff q t
  let L : ℝ := 1 + Real.log m
  let x : ℝ := 1 / (274877906944 * L ^ 9)
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hm : 2 ≤ m := by
    simpa only [m] using two_le_conductorHeightCutoff χ hχ t
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ t
  have hL : 1 < L := by dsimp only [L]; linarith
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (show 0 < 274877906944 * L ^ 9 by positivity)]
    have hLpow : 1 ≤ L ^ 9 := one_le_pow₀ hL.le
    nlinarith
  have hxlog : x ≤ 1 / Real.log m := by
    apply one_div_le_one_div_of_le hlogm
    calc
      Real.log (m : ℝ) ≤ L := by dsimp only [L]; linarith
      _ = L ^ 1 := by ring
      _ ≤ L ^ 9 := pow_le_pow_right₀ hL.le (by norm_num)
      _ ≤ 274877906944 * L ^ 9 :=
        le_mul_of_one_le_left (pow_nonneg hL0.le 9) (by norm_num)
  have hσ : 1 < 1 + x := by linarith
  have hσtwo : 1 + x ≤ 2 := by linarith
  have hχsqvalue :
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ ≤ 64 * L := by
    let m₂ := dirichletLConductorHeightCutoff q (2 * t)
    have hm₂ : 2 ≤ m₂ := by
      simpa only [m₂] using two_le_conductorHeightCutoff (χ ^ 2) hχsq (2 * t)
    have hlogm₂ : 0 < Real.log (m₂ : ℝ) := Real.log_pos (by exact_mod_cast hm₂)
    have hm₂m : m₂ ≤ m ^ 2 := by
      simpa only [m₂, m] using
        dirichletLConductorHeightCutoff_two_mul_le_sq χ hχ t
    have hlogle : Real.log (m₂ : ℝ) ≤ 2 * Real.log (m : ℝ) := by
      calc
        Real.log (m₂ : ℝ) ≤ Real.log ((m : ℕ) ^ 2 : ℕ) :=
          Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm₂))
            (by exact_mod_cast hm₂m)
        _ = 2 * Real.log (m : ℝ) := by
          push_cast
          rw [Real.log_pow]
          norm_num
    have hnear₂ : 1 - 1 / Real.log m₂ ≤ 1 + x := by
      have : 0 < 1 / Real.log m₂ := one_div_pos.mpr hlogm₂
      linarith
    have hv :=
      norm_LFunction_le_thirtytwo_mul_one_add_log_conductorHeightCutoff
        (χ ^ 2) hχsq (σ := 1 + x) (t := 2 * t)
        (by linarith) hσtwo (by simpa only [m₂] using hnear₂)
    calc
      ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖
          ≤ 32 * (1 + Real.log m₂) := by
            convert hv using 1; push_cast; ring
      _ ≤ 64 * L := by
        dsimp only [L]
        nlinarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ≤ 2 / x := by
    rw [DirichletCharacter.LFunctionTrivChar]
    calc
      ‖(1 : DirichletCharacter ℂ q).LFunction (1 + x)‖ ≤ 1 + 1 / x := by
        convert norm_dirichletLFunction_le
          (1 : DirichletCharacter ℂ q) (1 + x) 0 hσ using 1 <;> norm_num
      _ ≤ 2 / x := by
        rw [le_div_iff₀ hx]
        field_simp [ne_of_gt hx]
        linarith
  have hprod : 1 ≤
      ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
        ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
        ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := by
    have hp := χ.norm_LFunction_product_ge_one hx t
    convert (show 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + 2 * I * t)‖ by
        simpa only [norm_mul, norm_pow] using hp) using 1; ring
  have hmajor : 1 ≤
      (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
    calc
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + x)‖ ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 *
          ‖(χ ^ 2).LFunction (1 + x + I * (2 * t))‖ := hprod
      _ ≤ (2 / x) ^ 3 * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L) := by
        gcongr
  have hlower : x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
    have hs := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hx.le 3)
    calc
      x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * ((2 / x) ^ 3 *
          ‖χ.LFunction (1 + x + I * t)‖ ^ 4 * (64 * L)) := hs
      _ = 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := by
        field_simp [ne_of_gt hx]
        ring
  intro hzero
  have hβleft : 1 - x ≤ β := by simpa only [x, L, m] using hβ.1
  have hβlower : 1 / 2 ≤ β := by linarith
  have hβright : β < 1 + x := by linarith [hβ.2]
  have hdiff :
      ‖χ.LFunction (((1 + x : ℝ) : ℂ) + t * I) -
          χ.LFunction ((β : ℂ) + t * I)‖ ≤
        (64 * L ^ 2) * (1 + x - β) := by
    rw [← integral_deriv_LFunction_eq_sub χ hχ β (1 + x) t]
    convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
    · congr
      rw [_root_.abs_of_nonneg (sub_nonneg.mpr hβright.le)]
    · intro σ hσpath
      rw [uIoc_of_le hβright.le, mem_Ioc] at hσpath
      have hnear : 1 - 1 / Real.log m ≤ σ := by
        have : 1 - 1 / Real.log m ≤ 1 - x := by linarith
        exact this.trans (hβleft.trans hσpath.1.le)
      have hd :=
        norm_deriv_LFunction_le_sixtyfour_mul_one_add_log_sq_conductorHeightCutoff
          χ hχ (σ := σ) (t := t)
          (hβlower.trans hσpath.1.le) (hσpath.2.trans hσtwo)
          (by simpa only [m] using hnear)
      convert hd using 1; ring
  have hright : ‖χ.LFunction (1 + x + I * t)‖ ≤ 128 * L ^ 2 * x := by
    have hzero' : χ.LFunction (β + t * I) = 0 := by
      convert hzero using 1; ring
    rw [hzero', sub_zero] at hdiff
    have harg : (((1 + x : ℝ) : ℂ) + t * I) = 1 + x + I * t := by
      push_cast
      ring
    rw [harg] at hdiff
    calc
      ‖χ.LFunction (1 + x + I * t)‖ ≤ (64 * L ^ 2) * (1 + x - β) := hdiff
      _ ≤ (64 * L ^ 2) * (2 * x) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 128 * L ^ 2 * x := by ring
  have hcontr : x ^ 3 ≤ 512 * 128 ^ 4 * L ^ 9 * x ^ 4 := by
    calc
      x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := hlower
      _ ≤ 512 * L * (128 * L ^ 2 * x) ^ 4 := by gcongr
      _ = 512 * 128 ^ 4 * L ^ 9 * x ^ 4 := by ring
  have hpay : 512 * 128 ^ 4 * L ^ 9 * x ^ 4 = x ^ 3 / 2 := by
    dsimp only [x]
    field_simp [ne_of_gt hL0]
    ring
  rw [hpay] at hcontr
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  linarith

end AnalyticNumberTheory.LargeSieve