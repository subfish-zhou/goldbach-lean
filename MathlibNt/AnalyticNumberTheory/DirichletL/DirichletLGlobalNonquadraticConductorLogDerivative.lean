module

public import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLGlobalNonquadraticConductorLogZeroFree

/-!
# Sharp conductor-logarithmic nonquadratic logarithmic derivative bound

The product argument is retained quantitatively: first it gives a lower bound
for the L-value throughout a narrower strip, and that lower bound is then
divided into the sharp derivative estimate.  No positive power of the modulus
or height occurs.
-/

@[expose] public section

open Complex Set

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogValueBound
open DirichletLGlobalConductorLogDerivativeBound
open DirichletLWeakStripDifferenceBound

/-- Quantitative nonquadratic lower bound in the sharp conductor-log strip. -/
theorem norm_LFunction_lower_of_nonquadratic_conductorLog
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 ≠ 1)
    {β t : ℝ}
    (hβ : β ∈ Set.Ico
      (1 - 1 / (4398046511104 *
        (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) 1) :
    128 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 *
        (1 / (4398046511104 *
          (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 9)) ≤
      ‖χ.LFunction (β + I * t)‖ := by
  let m : ℕ := dirichletLConductorHeightCutoff q t
  let L : ℝ := 1 + Real.log m
  let x : ℝ := 1 / (4398046511104 * L ^ 9)
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h, one_pow]
  have hlogm : 0 < Real.log (m : ℝ) := by
    simpa only [m] using log_conductorHeightCutoff_pos χ hχ t
  have hL : 1 < L := by dsimp only [L]; linarith
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hwidth := nonquadraticConductorLogWidth_bounds (A := 4398046511104) (by norm_num) hlogm
  have hx : 0 < x := hwidth.1
  have hxhalf : x ≤ 1 / 2 := hwidth.2.1
  have hxlog : x ≤ 1 / Real.log m := hwidth.2.2
  have hlower := nonquadratic_conductorLog_product_lower χ hχsq t hx hxhalf
  have hβleft : 1 - x ≤ β := by simpa only [x, L, m] using hβ.1
  have hβright : β < 1 + x := by linarith [hβ.2]
  have hdiff := norm_LFunction_horizontal_conductorLog_le χ hχ (t := t)
    hxhalf hxlog hβleft hβright
  have hdiff' :
      ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ ≤
        128 * L ^ 2 * x := by
    have harg₁ : (((1 + x : ℝ) : ℂ) + t * I) = 1 + x + I * t := by
      push_cast
      ring
    have hargβ : ((β : ℂ) + t * I) = β + I * t := by
      ring
    rw [harg₁, hargβ] at hdiff
    calc
      _ ≤ (64 * L ^ 2) * (1 + x - β) := hdiff
      _ ≤ (64 * L ^ 2) * (2 * x) := by
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 128 * L ^ 2 * x := by ring
  change 128 * L ^ 2 * x ≤ ‖χ.LFunction (β + I * t)‖
  by_contra hnot
  have hleft : ‖χ.LFunction (β + I * t)‖ < 128 * L ^ 2 * x := lt_of_not_ge hnot
  have hright : ‖χ.LFunction (1 + x + I * t)‖ < 256 * L ^ 2 * x := by
    calc
      ‖χ.LFunction (1 + x + I * t)‖ ≤
          ‖χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t)‖ +
            ‖χ.LFunction (β + I * t)‖ := by
              simpa only [sub_add_cancel] using norm_add_le
                (χ.LFunction (1 + x + I * t) - χ.LFunction (β + I * t))
                (χ.LFunction (β + I * t))
      _ < 128 * L ^ 2 * x + 128 * L ^ 2 * x := add_lt_add_of_le_of_lt hdiff' hleft
      _ = 256 * L ^ 2 * x := by ring
  have hpow : ‖χ.LFunction (1 + x + I * t)‖ ^ 4 <
      (256 * L ^ 2 * x) ^ 4 :=
    pow_lt_pow_left₀ hright (norm_nonneg _) (by norm_num)
  have hcontr : x ^ 3 < 512 * 256 ^ 4 * L ^ 9 * x ^ 4 := by
    calc
      x ^ 3 ≤ 512 * L * ‖χ.LFunction (1 + x + I * t)‖ ^ 4 := hlower
      _ < 512 * L * (256 * L ^ 2 * x) ^ 4 :=
        mul_lt_mul_of_pos_left hpow (by positivity)
      _ = 512 * 256 ^ 4 * L ^ 9 * x ^ 4 := by ring
  have hpay : 512 * 256 ^ 4 * L ^ 9 * x ^ 4 = x ^ 3 / 2 := by
    dsimp only [x]
    field_simp [ne_of_gt hL0]
    ring
  rw [hpay] at hcontr
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  linarith


end AnalyticNumberTheory.LargeSieve