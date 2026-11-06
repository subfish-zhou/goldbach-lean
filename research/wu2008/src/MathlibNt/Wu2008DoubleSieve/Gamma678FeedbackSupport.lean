import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackActual

/-! Exact support enclosures, boundary guards, and denominator positivity. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval


theorem kernel_support (j : Kind) : Function.support (K j) ⊆ Icc (vLo j) (vHi j) := by
  intro v hv
  by_contra hn
  have he (t : ℝ) : masked j v t = 0 := if_neg (fun h => hn (slice_bounds h).1)
  exact hv (by rw [← slice_integral]; simp only [he, integral_zero])


theorem endpoint_widths (j : Kind) : U j (vLo j) = L j (vLo j) ∧ U j (vHi j) = L j (vHi j) := by
  cases j <;> norm_num [U, L, vLo, vHi, invU, gamma5FeedbackW, gamma5ClassicalS, S, a, b, c, f]


theorem kernel_nonnegative (j : Kind) (v : ℝ) : 0 ≤ K j v := by
  rw [← slice_integral]
  exact integral_nonneg (fun t => (masked_bounds j v t).1)




end Wu2008DoubleSieve.Gamma678Feedback
