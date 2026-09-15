import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Evaluation of the literal tail-loss integral

The integrand and endpoints are exactly those in `tailOriginalSum_sharp_upper`.
All logarithms are evaluated at positive arguments, away from both poles.
-/

namespace Wu2004MeanValue

open Set
noncomputable section

theorem loss_tau_bounds (a : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2) :
    1 / 3 < (a - 1) / a ∧ (a - 1) / a < 1 / 2 := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply (lt_div_iff₀ ha0).mpr
    linarith
  · apply (div_lt_iff₀ ha0).mpr
    linarith

theorem tail_kernel_domain {τ u : ℝ} (hτ : 0 < τ)
    (hu : u ∈ Icc τ (1 / 2 : ℝ)) :
    0 < u ∧ 0 < 1 - u ∧ 0 < u * (1 - u) := by
  have hu0 : 0 < u := hτ.trans_le hu.1
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  exact ⟨hu0, hu1, mul_pos hu0 hu1⟩

theorem tail_kernel_integral_eq_log (τ : ℝ) (hτ : 0 < τ) (hτh : τ < 1 / 2) :
    (∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
      Real.log ((1 - τ) / τ) := by
  have hdom : ∀ u ∈ uIcc τ (1 / 2 : ℝ), 0 < u ∧ 0 < 1 - u ∧
      0 < u * (1 - u) := by
    simpa only [uIcc_of_le hτh.le] using
      (fun u hu => tail_kernel_domain hτ (u := u) hu)
  have hcont : ContinuousOn (fun u : ℝ => 1 / (u * (1 - u)))
      (uIcc τ (1 / 2 : ℝ)) :=
    continuousOn_const.div
      (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
      (fun u hu => (hdom u hu).2.2.ne')
  have hderiv : ∀ u ∈ uIcc τ (1 / 2 : ℝ),
      HasDerivAt (fun u : ℝ => Real.log u - Real.log (1 - u))
        (1 / (u * (1 - u))) u := by
    intro u hu
    obtain ⟨hu0, hu1, _⟩ := hdom u hu
    convert! (Real.hasDerivAt_log hu0.ne').sub
      (((hasDerivAt_id u).const_sub 1).log hu1.ne') using 1
    change 1 / (u * (1 - u)) = u⁻¹ - -1 / (1 - u)
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  have ht1 : 0 < 1 - τ := by linarith
  rw [Real.log_div ht1.ne' hτ.ne']
  convert hFTC using 1
  norm_num

theorem loss_integral_eq_log (a : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2) :
    8 * (∫ u in (a - 1) / a..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
      8 * Real.log (1 / (a - 1)) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  obtain ⟨hτ, hτh⟩ := loss_tau_bounds a ha ha2
  rw [tail_kernel_integral_eq_log _ (by linarith) hτh]
  congr 2
  field_simp
  ring

theorem loss_log_pos (a : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2) :
    0 < Real.log (1 / (a - 1)) := by
  have ha1 : 0 < a - 1 := by linarith
  apply Real.log_pos
  apply (lt_div_iff₀ ha1).mpr
  linarith

end
end Wu2004MeanValue
