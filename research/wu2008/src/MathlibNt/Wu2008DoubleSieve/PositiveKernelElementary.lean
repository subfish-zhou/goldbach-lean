import MathlibNt.Wu2008DoubleSieve.FourthRowClassicalCoefficientLog

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- The fixed global logarithmic lower inequality; no finite approximation is used. -/
theorem positiveKernel_log_lower {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ log x := by
  let f : ℝ → ℝ := fun t => log t - 2 * (t - 1) / (t + 1)
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :
      HasDerivAt f ((t - 1)^2 / (t * (t + 1)^2)) t := by
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have ht1 : t + 1 ≠ 0 := by linarith [ht.1]
    convert! (hasDerivAt_log ht0).sub
      ((((hasDerivAt_id t).sub_const 1).const_mul 2).div
        ((hasDerivAt_id t).add_const 1) ht1) using 1
    dsimp [f]
    field_simp
    ring
  have hm : MonotoneOn f (Icc 1 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => div_nonneg (sq_nonneg _) (by
        have h := (interior_subset ht : t ∈ Icc 1 x).1
        positivity))
  have h := hm (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  dsimp [f] at h
  simpa using h

/-- The fixed global logarithmic upper inequality. -/
theorem positiveKernel_log_upper {x : ℝ} (hx : 1 ≤ x) :
    log x ≤ (x^2 - 1) / (2 * x) := by
  let f : ℝ → ℝ := fun t => (t^2 - 1) / (2 * t) - log t
  have hd (t : ℝ) (ht : t ∈ Icc 1 x) :
      HasDerivAt f ((t - 1)^2 / (2 * t^2)) t := by
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    convert! ((((hasDerivAt_id t).pow 2).sub_const 1).div
      ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht0)).sub
      (hasDerivAt_log ht0) using 1
    dsimp [f]
    field_simp
    ring
  have hm : MonotoneOn f (Icc 1 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t _ => div_nonneg (sq_nonneg _) (by positivity))
  have h := hm (left_mem_Icc.mpr hx) (right_mem_Icc.mpr hx) hx
  dsimp [f] at h
  simpa using h

/-- The reciprocal weight lies below its endpoint chord, proved by an exact residual. -/
theorem positiveKernel_chord {h z : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hz : z ∈ Icc 0 h) :
    1 / ((3 - 2*z) * (2-z)) ≤
      (1-z/h) / 6 + (z/h) / ((3-2*h)*(2-h)) := by
  have hd : 0 < (3-2*z)*(2-z) := mul_pos (by linarith [hz.2]) (by linarith [hz.2])
  have he : 0 < (3-2*h)*(2-h) := mul_pos (by linarith) (by linarith)
  have hp : 0 ≤ 37-14*h-14*z+4*h*z := by
    have hz1 : z < 1 := hz.2.trans_lt hh1
    have hhz : 0 ≤ h*z := mul_nonneg hh.le hz.1
    linarith
  have hid : (1-z/h) / 6 + (z/h) / ((3-2*h)*(2-h)) -
      1 / ((3-2*z)*(2-z)) =
      z*(h-z)*(37-14*h-14*z+4*h*z) /
        (6*((3-2*h)*(2-h))*((3-2*z)*(2-z))) := by
    have hz3 : 3-2*z ≠ 0 := ne_of_gt (by linarith [hz.2])
    have hz2 : 2-z ≠ 0 := ne_of_gt (by linarith [hz.2])
    have hh3 : 3-2*h ≠ 0 := ne_of_gt (by linarith)
    have hh2 : 2-h ≠ 0 := ne_of_gt (by linarith)
    field_simp [hh.ne', hz3, hz2, hh3, hh2, show 3-z*2 ≠ 0 by linarith [hz.2],
      show 3-h*2 ≠ 0 by linarith]
    ring
  have hn : 0 ≤ z*(h-z)*(37-14*h-14*z+4*h*z) /
      (6*((3-2*h)*(2-h))*((3-2*z)*(2-z))) :=
    div_nonneg (mul_nonneg (mul_nonneg hz.1 (sub_nonneg.mpr hz.2)) hp)
      (le_of_lt (mul_pos (mul_pos (by norm_num) he) hd))
  linarith [hid]

end Wu2008DoubleSieve
