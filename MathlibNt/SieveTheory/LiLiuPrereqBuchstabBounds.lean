import MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Global bounds for the Buchstab function

The global integral equation propagates the interval `[1/2, 1]` from
`[1, 2]` to every subsequent unit interval.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace LiLiuPrereqBuchstab

private theorem buchstab_bounds_initial {u : ℝ} (hu : 1 ≤ u) (hu₂ : u ≤ 2) :
    1 / 2 ≤ buchstab u ∧ buchstab u ≤ 1 := by
  rw [buchstab_eq_one_div hu hu₂]
  have hu₀ : 0 < u := by linarith
  constructor
  · apply (le_div_iff₀ hu₀).mpr
    linarith
  · apply (div_le_iff₀ hu₀).mpr
    linarith

private theorem buchstab_bounds_on_stage (n : ℕ) :
    ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 →
      1 / 2 ≤ buchstab u ∧ buchstab u ≤ 1 := by
  induction n with
  | zero =>
      intro u hu hu₂
      exact buchstab_bounds_initial hu (by simpa using hu₂)
  | succ n ih =>
      intro u hu hupper
      by_cases hu₂ : u ≤ 2
      · exact buchstab_bounds_initial hu hu₂
      have h₂ : 2 ≤ u := le_of_lt (lt_of_not_ge hu₂)
      have hu₀ : 0 < u := by linarith
      have hi : IntervalIntegrable (fun t : ℝ => buchstab (t - 1)) volume 2 u :=
        (continuous_buchstab.comp (continuous_id.sub continuous_const)).intervalIntegrable 2 u
      have hb : ∀ t ∈ Icc (2 : ℝ) u,
          1 / 2 ≤ buchstab (t - 1) ∧ buchstab (t - 1) ≤ 1 := by
        intro t ht
        apply ih (t - 1)
        · linarith [ht.1]
        · push_cast at hupper
          linarith [ht.2]
      have hlo := intervalIntegral.integral_mono_on h₂
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 2 u)
        hi (fun t ht => (hb t ht).1)
      have hhi := intervalIntegral.integral_mono_on h₂ hi
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 2 u)
        (fun t ht => (hb t ht).2)
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
      have he := mul_buchstab_eq_integral h₂
      constructor
      · apply (mul_le_mul_iff_left₀ hu₀).mp
        nlinarith
      · apply (mul_le_mul_iff_left₀ hu₀).mp
        nlinarith

/-- The two-sided bound holds on the entire prescribed domain, without an
upper cutoff or an analytic hypothesis. -/
theorem buchstab_bounds {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 ≤ buchstab u ∧ buchstab u ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  exact buchstab_bounds_on_stage n u hu (by linarith)

theorem one_half_le_buchstab {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 ≤ buchstab u :=
  (buchstab_bounds hu).1

theorem buchstab_le_one {u : ℝ} (hu : 1 ≤ u) :
    buchstab u ≤ 1 :=
  (buchstab_bounds hu).2

theorem buchstab_pos {u : ℝ} (hu : 1 ≤ u) : 0 < buchstab u := by
  have h := one_half_le_buchstab hu
  linarith

theorem buchstab_nonneg {u : ℝ} (hu : 1 ≤ u) : 0 ≤ buchstab u :=
  (buchstab_pos hu).le

theorem buchstab_ne_zero {u : ℝ} (hu : 1 ≤ u) : buchstab u ≠ 0 :=
  (buchstab_pos hu).ne'

/-- In particular, the Buchstab factor in a denominator is uniformly safe. -/
theorem one_div_buchstab_bounds {u : ℝ} (hu : 1 ≤ u) :
    1 ≤ 1 / buchstab u ∧ 1 / buchstab u ≤ 2 := by
  have hp := buchstab_pos hu
  have hb := buchstab_bounds hu
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith [hb.2]
  · apply (div_le_iff₀ hp).mpr
    linarith [hb.1]

/-- The first delayed interval has the familiar logarithmic formula,
including both endpoints. -/
theorem buchstab_eq_log_div {u : ℝ} (hu₂ : 2 ≤ u) (hu₃ : u ≤ 3) :
    buchstab u = (1 + Real.log (u - 1)) / u := by
  have hd : ∀ t ∈ uIcc (2 : ℝ) u,
      HasDerivAt (fun v : ℝ => Real.log (v - 1)) (buchstab (t - 1)) t := by
    intro t ht
    rw [uIcc_of_le hu₂] at ht
    have ht₁ : 1 ≤ t - 1 := by linarith [ht.1]
    rw [buchstab_eq_one_div ht₁ (by linarith [ht.2])]
    simpa using ((hasDerivAt_id t).sub_const 1).log (by linarith : t - 1 ≠ 0)
  have hi : IntervalIntegrable (fun t : ℝ => buchstab (t - 1)) volume 2 u :=
    (continuous_buchstab.comp (continuous_id.sub continuous_const)).intervalIntegrable 2 u
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.log_one, sub_zero] at he
  apply (eq_div_iff (by linarith : u ≠ 0)).mpr
  nlinarith [mul_buchstab_eq_integral hu₂]

/-- The derivative form of the Buchstab equation, valid for every `u > 2`. -/
theorem hasDerivAt_buchstab {u : ℝ} (hu : 2 < u) :
    HasDerivAt buchstab ((buchstab (u - 1) - buchstab u) / u) u := by
  have hu₀ : 0 < u := by linarith
  have hd₀ := (hasDerivAt_mul_buchstab hu).div (hasDerivAt_id u) hu₀.ne'
  have he : (buchstab (u - 1) * u - (u * buchstab u) * 1) / u ^ 2 =
      (buchstab (u - 1) - buchstab u) / u := by
    field_simp
  have hd : HasDerivAt (fun v : ℝ => (v * buchstab v) / v)
      ((buchstab (u - 1) - buchstab u) / u) u := by
    change HasDerivAt (fun v : ℝ => (v * buchstab v) / v)
      ((buchstab (u - 1) * u - (u * buchstab u) * 1) / u ^ 2) u at hd₀
    rwa [he] at hd₀
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu₀] with v hv
  field_simp

theorem deriv_buchstab {u : ℝ} (hu : 2 < u) :
    deriv buchstab u = (buchstab (u - 1) - buchstab u) / u :=
  (hasDerivAt_buchstab hu).deriv

/-- The global range bounds give a decaying absolute derivative bound. -/
theorem abs_deriv_buchstab_le {u : ℝ} (hu : 2 < u) :
    |deriv buchstab u| ≤ 1 / (2 * u) := by
  have hu₀ : 0 < u := by linarith
  have hb := buchstab_bounds (by linarith : 1 ≤ u)
  have hd := buchstab_bounds (by linarith : 1 ≤ u - 1)
  have hdiff : |buchstab (u - 1) - buchstab u| ≤ 1 / 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hb.1, hb.2, hd.1, hd.2]
  calc
    |deriv buchstab u| = |buchstab (u - 1) - buchstab u| / u := by
      rw [deriv_buchstab hu, abs_div, abs_of_pos hu₀]
    _ ≤ (1 / 2) / u := div_le_div_of_nonneg_right hdiff hu₀.le
    _ = 1 / (2 * u) := by ring

end LiLiuPrereqBuchstab