import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosurePolynomials
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
open Set MeasureTheory Polynomial
namespace LiLiuBuchstabSharp

private theorem closure_log_two : Real.log 2 ≤ (69314718057 / 100000000000 : ℝ) := by
  have h := logLower_twelve_error (x := 2) (by norm_num) (by norm_num)
  have hc : logLower 12 2 + (1 / 100000000000 : ℝ) ≤
      (69314718057 / 100000000000 : ℝ) := by
    norm_num [logLower, Finset.sum_range_succ]
  linarith [h.2]

/-- Concrete degree-32 polynomial majorant on the full seed interval. -/
theorem closure_seed_upper {u : ℝ} (hu : 2 ≤ u) (hu' : u ≤ 3) :
    rationalStage 0 u ≤ closureP0.eval (3-u) := by
  let W : Polynomial ℝ := (C 3 - X) * closureP0
  let F : ℝ → ℝ := fun x => W.eval x - (1 + Real.log (2-x))
  have hd : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt F (W.derivative.eval x + 1 / (2-x)) x := by
    intro x hx
    have hx' : (2 : ℝ)-x ≠ 0 := by linarith [hx.2]
    convert (W.hasDerivAt x).sub
      ((((hasDerivAt_id x).const_sub 2).log hx').const_add 1) using 1 <;>
      (first | rfl | simp [div_eq_mul_inv])
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ W.derivative.eval x + 1/(2-x) := by
    intro x hx
    have hx' : (0 : ℝ) < 2-x := by linarith [hx.2]
    have he : (2-x) * W.derivative.eval x + 1 =
        x^32 * ((1 / 4294967296 : ℝ) + (1952169919770657109132782435831467 / 7557731879684753690355644655206400000000000 : ℝ) * (2-x)) := by
      dsimp [W]
      simp only [closureP0, derivative_mul, derivative_sub, derivative_add,
        derivative_C, derivative_X, eval_add, eval_sub, eval_mul,
        eval_C, eval_X, eval_zero, eval_one]
      ring
    have hp : 0 ≤ x^32 * ((1 / 4294967296 : ℝ) + (1952169919770657109132782435831467 / 7557731879684753690355644655206400000000000 : ℝ) * (2-x)) := by positivity
    have hdpos : 0 ≤ ((2-x) * W.derivative.eval x + 1) / (2-x) :=
      div_nonneg (by linarith [he]) hx'.le
    convert hdpos using 1
    field_simp
  have hm : MonotoneOn F (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · apply ContinuousOn.sub W.continuous.continuousOn
      apply continuousOn_const.add
      apply ContinuousOn.log (continuous_const.sub continuous_id).continuousOn
      intro x hx
      change 2-x ≠ 0
      linarith [hx.2]
    · intro x hx
      have hxi : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
      exact (hd x hxi).hasDerivWithinAt
    · intro x hx
      exact hpos x (interior_subset hx)
  have hbase : 0 ≤ F 0 := by
    have h := closure_log_two
    norm_num [F, W, closureP0] at ⊢
    linarith
  have hf := hm (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 3-u ∈ Icc (0 : ℝ) 1 by constructor <;> linarith) (by linarith : 0 ≤ 3-u)
  have hweight : 1 + Real.log (u-1) ≤ u * closureP0.eval (3-u) := by
    have he : (2 : ℝ)-(3-u)=u-1 := by ring
    have hF := le_trans hbase hf
    dsimp [F, W] at hF
    simp only [eval_mul, eval_sub, eval_C, eval_X, he] at hF
    nlinarith
  have hr := (rationalStage_error 0 (u := u) (by simpa) (by simpa)).1
  have hω := LiLiuPrereqBuchstab.buchstab_eq_log_div hu hu'
  rw [hω] at hr
  have hup : 0 < u := by linarith
  have hdiv : (1 + Real.log (u-1))/u ≤ closureP0.eval (3-u) :=
    (div_le_iff₀ hup).mpr (by nlinarith [hweight])
  linarith

end LiLiuBuchstabSharp