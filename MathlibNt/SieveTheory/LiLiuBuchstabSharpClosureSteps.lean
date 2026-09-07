import MathlibNt.SieveTheory.LiLiuBuchstabSharpClosureSeed
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
open Set MeasureTheory Polynomial
namespace LiLiuBuchstabSharp

private theorem closure_step_upper {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ} (hf : Continuous f) (P A Q : Polynomial ℝ)
    (hA : A.derivative = P)
    (hprev : ∀ v ∈ Icc (a-1) a, f v ≤ P.eval (a-v))
    (hcert : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ (a+1-x)*Q.eval x - (a*P.eval 0 + A.eval 1 - A.eval x))
    {u : ℝ} (hu : a ≤ u) (hu' : u ≤ a+1) :
    rationalStep a f u ≤ Q.eval (a+1-u) := by
  have hup : 0 < u := lt_of_lt_of_le ha hu
  have hp : Continuous (fun t : ℝ => P.eval (a+1-t)) :=
    P.continuous.comp (continuous_const.sub continuous_id)
  have hfp : Continuous (fun t : ℝ => f (t-1)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hu
    (hfp.intervalIntegrable a u) (hp.intervalIntegrable a u) (fun t ht => by
      have h := hprev (t-1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      convert h using 1
      congr 1
      ring)
  have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -A.eval (a+1-t))
      (P.eval (a+1-t)) t := by
    intro t
    convert ((A.hasDerivAt (a+1-t)).comp t ((hasDerivAt_id t).const_sub (a+1))).neg using 1 <;>
      (first | rfl | simp [hA])
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hder t) (hp.intervalIntegrable a u)
  have hz : a+1-a = (1 : ℝ) := by ring
  rw [he, hz] at hi
  have hb := hprev a ⟨by linarith, le_rfl⟩
  rw [sub_self] at hb
  have hc := hcert (a+1-u) ⟨by linarith, by linarith⟩
  unfold rationalStep
  rw [max_eq_right hu]
  apply (div_le_iff₀ hup).mpr
  nlinarith [mul_le_mul_of_nonneg_left hb ha.le]

-- Concrete stages

/-- The explicit polynomial majorizes the actual integral expression on a full unit interval. -/
theorem closure_stage1_upper {u : ℝ} (hu : 3 ≤ u) (hu' : u ≤ 4) :
    rationalStage 1 u ≤ closureP1.eval (4-u) := by
  have hA : closureA0.derivative = closureP0 := by
    apply Polynomial.funext
    intro x
    simp only [closureA0, closureP0, derivative_add, derivative_mul, derivative_C,
      derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
    ring
  have hcert : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ (4-x)*closureP1.eval x -
        (3*closureP0.eval 0 + closureA0.eval 1 - closureA0.eval x) := by
    intro x hx
    have he : (4-x)*closureP1.eval x -
        (3*closureP0.eval 0 + closureA0.eval 1 - closureA0.eval x) =
        (4124224922206591655910363373724158538026715189951723953 / 96953973119257903992088233810080237834285286351930654720000000000000 : ℝ) * x^34 * (1-x) := by
      simp only [closureP1, closureP0, closureA0, eval_add, eval_mul, eval_C, eval_X]
      ring
    rw [he]
    have hx0 := hx.1
    have hx1 : 0 ≤ 1-x := by linarith [hx.2]
    positivity
  have hprev : ∀ v ∈ Icc (3-1 : ℝ) 3,
      rationalStage 0 v ≤ closureP0.eval (3-v) := by
    intro v hv
    exact closure_seed_upper (by linarith [hv.1]) hv.2
  have h := closure_step_upper (a := 3) (by norm_num)
    (continuous_rationalStage 0) closureP0 closureA0 closureP1 hA hprev
    (by simpa only [show (3 : ℝ)+1=4 by norm_num] using hcert) hu (by linarith)
  convert h using 1 <;> norm_num [rationalStage]

/-- The explicit polynomial majorizes the actual integral expression on a full unit interval. -/
theorem closure_stage2_upper {u : ℝ} (hu : 4 ≤ u) (hu' : u ≤ 5) :
    rationalStage 2 u ≤ closureP2.eval (5-u) := by
  have hA : closureA1.derivative = closureP1 := by
    apply Polynomial.funext
    intro x
    simp only [closureA1, closureP1, derivative_add, derivative_mul, derivative_C,
      derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
    ring
  have hcert : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ (5-x)*closureP2.eval x -
        (4*closureP1.eval 0 + closureA1.eval 1 - closureA1.eval x) := by
    intro x hx
    have he : (5-x)*closureP2.eval x -
        (4*closureP1.eval 0 + closureA1.eval 1 - closureA1.eval x) =
        (23243515360769595682769712795564914532697087193055196939267659207492217096858499212903994201 / 45362662409477910911981489358253790693135394222882422784000000000000000000000000000000000000000000000000000 : ℝ) * x^36 := by
      simp only [closureP2, closureP1, closureA1, eval_add, eval_mul, eval_C, eval_X]
      ring
    rw [he]
    have hx0 := hx.1
    have hx1 : 0 ≤ 1-x := by linarith [hx.2]
    positivity
  have hprev : ∀ v ∈ Icc (4-1 : ℝ) 4,
      rationalStage 1 v ≤ closureP1.eval (4-v) := by
    intro v hv
    exact closure_stage1_upper (by linarith [hv.1]) hv.2
  have h := closure_step_upper (a := 4) (by norm_num)
    (continuous_rationalStage 1) closureP1 closureA1 closureP2 hA hprev
    (by simpa only [show (4 : ℝ)+1=5 by norm_num] using hcert) hu (by linarith)
  convert h using 1 <;> norm_num [rationalStage]

/-- The explicit polynomial majorizes the actual integral expression on a full unit interval. -/
theorem closure_stage3_upper {u : ℝ} (hu : 5 ≤ u) (hu' : u ≤ 6) :
    rationalStage 3 u ≤ closureP3.eval (6-u) := by
  have hA : closureA2.derivative = closureP2 := by
    apply Polynomial.funext
    intro x
    simp only [closureA2, closureP2, derivative_add, derivative_mul, derivative_C,
      derivative_X, eval_add, eval_mul, eval_C, eval_X, eval_zero, eval_one]
    ring
  have hcert : ∀ x ∈ Icc (0 : ℝ) 1,
      0 ≤ (6-x)*closureP3.eval x -
        (5*closureP2.eval 0 + closureA2.eval 1 - closureA2.eval x) := by
    intro x hx
    have he : (6-x)*closureP3.eval x -
        (5*closureP2.eval 0 + closureA2.eval 1 - closureA2.eval x) =
        (690415181308757414259992884280325618011275660968370627881227519160354068072444209893623877299466003439721987883505770750723710903 / 842368147479174823452709259249214713917701951335282163357846237477147855709395085139660570099712000000000000000000000000000000000000000000000000000 : ℝ) * x^37 * (1-x) := by
      simp only [closureP3, closureP2, closureA2, eval_add, eval_mul, eval_C, eval_X]
      ring
    rw [he]
    have hx0 := hx.1
    have hx1 : 0 ≤ 1-x := by linarith [hx.2]
    positivity
  have hprev : ∀ v ∈ Icc (5-1 : ℝ) 5,
      rationalStage 2 v ≤ closureP2.eval (5-v) := by
    intro v hv
    exact closure_stage2_upper (by linarith [hv.1]) hv.2
  have h := closure_step_upper (a := 5) (by norm_num)
    (continuous_rationalStage 2) closureP2 closureA2 closureP3 hA hprev
    (by simpa only [show (5 : ℝ)+1=6 by norm_num] using hcert) hu (by linarith)
  convert h using 1 <;> norm_num [rationalStage]

end LiLiuBuchstabSharp