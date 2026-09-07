import MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The exact Buchstab logarithmic integral

The primitive `-(L / log t) * buchstab (L / log t) / L` evaluates the
logarithmic kernel. The fundamental theorem is used only on the interior:
the upper endpoint, where the Buchstab argument is `2`, needs continuity
but not differentiability. In particular the square endpoint is included.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace LiLiuPrereqBuchstab

/-- The antiderivative of the logarithmic Buchstab kernel, away from the
initial-condition corner. -/
theorem hasDerivAt_buchstab_log_primitive {L t : ℝ}
    (ht : 1 < t) (hLt : 2 < L / Real.log t) :
    HasDerivAt
      (fun s : ℝ => -((L / Real.log s) * buchstab (L / Real.log s)) / L)
      (buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2)) t := by
  have ht₀ : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hL : L ≠ 0 := by
    have := (lt_div_iff₀ hlog).mp hLt
    nlinarith
  have hd := (hasDerivAt_const t L).div (Real.hasDerivAt_log ht₀) hlog.ne'
  have hc := (((hasDerivAt_mul_buchstab hLt).comp t hd).neg).div_const L
  have he : -(buchstab (L / Real.log t - 1) *
      ((0 * Real.log t - L * t⁻¹) / (Real.log t) ^ 2)) / L =
      buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2) := by
    field_simp
    ring
  rw [he] at hc
  exact hc

/-- The logarithmic kernel is integrable on every compact interval above `1`. -/
theorem intervalIntegrable_buchstab_log_kernel {a b : ℝ} (L : ℝ)
    (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2))
      volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro t ht
  have ht₁ : 1 < t := lt_of_lt_of_le ha ht.1
  have ht₀ : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht₁)
  have hl₀ : Real.log t ≠ 0 := (Real.log_pos ht₁).ne'
  have hl : ContinuousAt Real.log t := Real.continuousAt_log ht₀
  have hv : ContinuousAt (fun s : ℝ => L / Real.log s) t :=
    continuousAt_const.div hl hl₀
  exact ((continuous_buchstab.continuousAt.comp (hv.sub continuousAt_const)).div
    (continuousAt_id.mul (hl.pow 2)) (mul_ne_zero ht₀ (pow_ne_zero 2 hl₀))).continuousWithinAt

/-- Exact evaluation with an arbitrary logarithmic numerator and an upper
endpoint whose transformed value is `2`. The interval may be degenerate. -/
theorem integral_buchstab_log_kernel {a b L : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hLb : L / Real.log b = 2) :
    (∫ t in a..b, buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2)) =
      ((L / Real.log a) * buchstab (L / Real.log a) - 1) / L := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hL : L = 2 * Real.log b := (div_eq_iff hlogb.ne').mp hLb
  have hcont : ContinuousOn
      (fun t : ℝ => -((L / Real.log t) * buchstab (L / Real.log t)) / L)
      (Icc a b) := by
    intro t ht
    have ht₁ : 1 < t := lt_of_lt_of_le ha ht.1
    have hl : ContinuousAt Real.log t :=
      Real.continuousAt_log (ne_of_gt (lt_trans zero_lt_one ht₁))
    have hv : ContinuousAt (fun s : ℝ => L / Real.log s) t :=
      continuousAt_const.div hl (Real.log_pos ht₁).ne'
    exact ((hv.mul (continuous_buchstab.continuousAt.comp hv)).neg.div_const L).continuousWithinAt
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt
        (fun s : ℝ => -((L / Real.log s) * buchstab (L / Real.log s)) / L)
        (buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2)) t := by
    intro t ht
    have ht₁ : 1 < t := lt_trans ha ht.1
    apply hasDerivAt_buchstab_log_primitive ht₁
    apply (lt_div_iff₀ (Real.log_pos ht₁)).mpr
    have hlt := Real.log_lt_log (lt_trans zero_lt_one ht₁) ht.2
    nlinarith
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv
    (intervalIntegrable_buchstab_log_kernel L ha hab)
  rw [hLb, buchstab_eq_one_div (by norm_num : (1 : ℝ) ≤ 2) le_rfl] at he
  calc
    _ = -(2 * (1 / 2)) / L -
        -((L / Real.log a) * buchstab (L / Real.log a)) / L := he
    _ = _ := by ring

/-- The corresponding exact change of variable `v = L / log t`. -/
theorem integral_buchstab_log_substitution {a b L : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hLb : L / Real.log b = 2) :
    (∫ t in a..b, buchstab (L / Real.log t - 1) / (t * (Real.log t) ^ 2)) =
      (∫ v in (2 : ℝ)..L / Real.log a, buchstab (v - 1)) / L := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le ha hab)
  have hL : L = 2 * Real.log b := (div_eq_iff hlogb.ne').mp hLb
  have hu : 2 ≤ L / Real.log a := by
    apply (le_div_iff₀ hloga).mpr
    have hlogab := Real.log_le_log (lt_trans zero_lt_one ha) hab
    linarith
  rw [integral_buchstab_log_kernel ha hab hLb, mul_buchstab_eq_integral hu]
  congr 1
  ring

/-- The upper logarithmic endpoint is exactly `2`, not merely asymptotic. -/
theorem log_div_log_sqrt {x : ℝ} (hx : 1 < x) :
    Real.log x / Real.log (Real.sqrt x) = 2 := by
  have hx₀ : 0 ≤ x := (lt_trans zero_lt_one hx).le
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.log_sqrt hx₀]
  field_simp

/-- The square-cutoff hypothesis places the lower transformed endpoint in
the domain of the Buchstab integral equation, including equality at `2`. -/
theorem two_le_log_div_log_of_sq_le {x y : ℝ}
    (hy : 1 < y) (hxy : y ^ 2 ≤ x) :
    2 ≤ Real.log x / Real.log y := by
  apply (le_div_iff₀ (Real.log_pos hy)).mpr
  have hlog := Real.log_le_log (sq_pos_of_pos (lt_trans zero_lt_one hy)) hxy
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- Exact unscaled evaluation on the interval from `y` to `sqrt x`. -/
theorem integral_buchstab_log_kernel_sqrt {x y : ℝ}
    (hy : 1 < y) (hxy : y ^ 2 ≤ x) :
    (∫ t in y..Real.sqrt x,
      buchstab (Real.log x / Real.log t - 1) / (t * (Real.log t) ^ 2)) =
      ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) /
        Real.log x := by
  have hx : 1 < x := by nlinarith
  exact integral_buchstab_log_kernel hy (Real.le_sqrt_of_sq_le hxy)
    (log_div_log_sqrt hx)

/-- Identity (I) in the compact-uniform rough-count argument. Both real
endpoints are exact, and `x = y²` is allowed. -/
theorem mul_integral_buchstab_log_kernel_sqrt {x y : ℝ}
    (hy : 1 < y) (hxy : y ^ 2 ≤ x) :
    x * (∫ t in y..Real.sqrt x,
      buchstab (Real.log x / Real.log t - 1) / (t * (Real.log t) ^ 2)) =
      x / Real.log x *
        ((Real.log x / Real.log y) * buchstab (Real.log x / Real.log y) - 1) := by
  rw [integral_buchstab_log_kernel_sqrt hy hxy]
  ring

end LiLiuPrereqBuchstab