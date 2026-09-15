import MathlibNt.Wu2004MeanValue.LossIntegral

/-!
# A positive exact margin at the manuscript's fixed parameter

The logarithm bound is analytic: the difference between its cubic upper
bound and the logarithm has derivative `x^3/(1+x)` on the nonnegative axis.
Only the subsequent rational comparisons use `norm_num`.
No quantitative lower estimate for any representation count is asserted.
-/

namespace Wu2004MeanValue

open Set
noncomputable section

theorem log_one_add_le_cubic (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hpos : ∀ t ∈ uIcc 0 x, 0 < 1 + t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => t ^ 3 / (1 + t)) (uIcc 0 x) :=
    (continuousOn_id.pow 3).div (continuousOn_const.add continuousOn_id)
      (fun t ht => (hpos t ht).ne')
  have hderiv : ∀ t ∈ uIcc 0 x, HasDerivAt F (t ^ 3 / (1 + t)) t := by
    intro t ht
    have ht0 := (hpos t ht).ne'
    convert! (((hasDerivAt_id t).sub ((hasDerivAt_id t).pow 2 |>.div_const 2)).add
      ((hasDerivAt_id t).pow 3 |>.div_const 3)).sub
      (((hasDerivAt_id t).const_add 1).log ht0) using 1
    change t ^ 3 / (1 + t) =
      1 - (2 * t ^ (2 - 1) * 1) / 2 + (3 * t ^ (3 - 1) * 1) / 3 -
        1 / (1 + t)
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..x, t ^ 3 / (1 + t) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    exact div_nonneg (pow_nonneg ht.1 _) (by linarith [ht.1])
  rw [hFTC] at hnonneg
  simpa only [F, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
    zero_div, sub_zero, zero_add, add_zero, Real.log_one, sub_nonneg] using hnonneg

theorem source_parameter_admissible :
    (3 / 2 : ℝ) < 9469 / 5000 ∧ (9469 / 5000 : ℝ) < 2 := by
  norm_num

theorem source_tau_eq :
    (((9469 / 5000 : ℝ) - 1) / (9469 / 5000)) = 4469 / 9469 := by
  norm_num

theorem source_loss_integral_eq :
    8 * (∫ u in (4469 / 9469 : ℝ)..(1 / 2 : ℝ), 1 / (u * (1 - u))) =
      8 * Real.log (5000 / 4469) := by
  simpa only [source_tau_eq,
    show (1 : ℝ) / (9469 / 5000 - 1) = 5000 / 4469 by norm_num] using
    loss_integral_eq_log (9469 / 5000) source_parameter_admissible.1
      source_parameter_admissible.2

theorem source_log_upper :
    Real.log (5000 / 4469) ≤ (20049953067 : ℝ) / 178509387418 := by
  have h := log_one_add_le_cubic (531 / 4469) (by norm_num)
  norm_num at h ⊢
  exact h

theorem source_margin_lower :
    (40157376391 : ℝ) / 89254693709000 ≤
      899 / 1000 - 8 * Real.log (5000 / 4469) := by
  linarith [source_log_upper]

theorem source_margin_pos :
    0 < (899 / 1000 : ℝ) - 8 * Real.log (5000 / 4469) := by
  exact lt_of_lt_of_le (by norm_num) source_margin_lower

theorem source_integral_margin_pos :
    0 < (899 / 1000 : ℝ) -
      8 * (∫ u in (4469 / 9469 : ℝ)..(1 / 2 : ℝ), 1 / (u * (1 - u))) := by
  rw [source_loss_integral_eq]
  exact source_margin_pos

end
end Wu2004MeanValue
