import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import Mathlib.NumberTheory.Chebyshev

/-!
# Effective Chebyshev theta estimate

This is the quantitative bridge from the PNTAnd estimate for `psi` to the
prime-only Chebyshev function `theta`. It is the analytic input used by the
Mertens partial-summation development.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Chebyshev

/-- The medium PNT error for `psi` transfers to `theta`, with the standard
`sqrt x` prime-power correction retained explicitly. -/
theorem chebyshevTheta_medium_error :
    ∃ c > 0,
      (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, hpsi⟩ := chebyshevPsi_medium_error
  refine ⟨c, hc, ?_⟩
  have htheta_psi : (Chebyshev.theta - Chebyshev.psi) =O[atTop] sqrt := by
    rw [show Chebyshev.theta - Chebyshev.psi =
      fun x => -((Chebyshev.psi - Chebyshev.theta) x) by
        funext x
        simp only [Pi.sub_apply, neg_sub]]
    exact Chebyshev.isBigO_psi_sub_theta_sqrt.neg_left
  have hsqrt : sqrt =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
    IsBigO.of_bound' <| eventually_atTop.2 ⟨1, fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg]
      · exact le_add_of_nonneg_right (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))
      · exact add_nonneg (sqrt_nonneg _) (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))⟩
  have hpsi_bound : (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
    IsBigO.of_bound' <| eventually_atTop.2 ⟨1, fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (le_of_lt (exp_pos _))),
        Real.norm_eq_abs, abs_of_nonneg]
      · exact le_add_of_nonneg_left (sqrt_nonneg _)
      · exact add_nonneg (sqrt_nonneg _) (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))⟩
  have hpsi' : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) := by
    change (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) at hpsi
    exact hpsi.trans hpsi_bound
  calc
    Chebyshev.theta - id =
        fun x => Chebyshev.theta x - Chebyshev.psi x + (Chebyshev.psi x - x) := by
      funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    _ =O[atTop] fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
      (htheta_psi.trans hsqrt).add hpsi'

/-- A coarser theta estimate in the form used by partial summation. -/
theorem chebyshevTheta_error :
    (Chebyshev.theta - id) =O[atTop] fun x : ℝ => x / log x := by
  obtain ⟨c, hc, hpsi⟩ := chebyshevPsi_medium_error
  have hlog : ∀ᶠ x : ℝ in atTop, log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.log_pos hx).ne'
  have hsqrt : sqrt =o[atTop] fun x : ℝ => x / log x := by
    apply (isLittleO_mul_iff_isLittleO_div (f := log) (g := sqrt) (h := id) hlog).mp
    simpa [mul_comm] using isLittleO_sqrt_mul_log
  have hpow :
      (fun x : ℝ => (log x ^ ((1 : ℝ) / 10)) ^ (-10 : ℝ))
        =ᶠ[atTop] fun x => log x ^ (-1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.rpow_mul (Real.log_nonneg hx)]
    norm_num
  have hdecay :
      (fun x : ℝ => exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => log x ^ (-1 : ℝ) := by
    exact
      ((isLittleO_exp_neg_mul_rpow_atTop hc (-10)).comp_tendsto
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp tendsto_log_atTop)).congr'
        (Eventually.of_forall fun _ => rfl) hpow
  have hmedium :
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => x / log x := by
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using
      (isBigO_refl id atTop).mul_isLittleO hdecay
  have hpsi' : (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x / log x :=
    hpsi.trans hmedium.isBigO
  have hdelta : (Chebyshev.psi - Chebyshev.theta) =O[atTop]
      fun x : ℝ => x / log x :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans hsqrt.isBigO
  calc
    Chebyshev.theta - id =
        (Chebyshev.psi - id) - (Chebyshev.psi - Chebyshev.theta) := by
      funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    _ =O[atTop] fun x : ℝ => x / log x := hpsi'.sub hdelta

/-- The endpoint error in the Abel formula for reciprocal-prime sums. -/
theorem chebyshevTheta_endpoint_error :
    (fun x : ℝ => (Chebyshev.theta x - x) / (x * log x)) =O[atTop]
      fun x : ℝ => 1 / (log x) ^ 2 := by
  have hkernel : (fun x : ℝ => (x * log x)⁻¹) =O[atTop]
      fun x : ℝ => (x * log x)⁻¹ :=
    isBigO_refl _ _
  have h := chebyshevTheta_error.mul hkernel
  refine h.congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp [div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp

end AnalyticNumberTheory.PrimeDistribution
