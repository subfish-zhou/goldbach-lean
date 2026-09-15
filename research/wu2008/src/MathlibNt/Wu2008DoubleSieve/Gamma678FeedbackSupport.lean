import MathlibNt.Wu2008DoubleSieve.Gamma678FeedbackActual

/-! Exact support enclosures, boundary guards, and denominator positivity. -/
namespace Wu2008DoubleSieve.Gamma678Feedback
open Real Set MeasureTheory
open scoped Classical Topology Interval

theorem image_values :
    vLo .six = 14626 / 11125 ∧ vHi .six = 12398 / 7275 ∧
    vLo .seven = 39 / 25 ∧ vHi .seven = 53 / 25 ∧
    vLo .eight = 9724 / 7275 ∧ vHi .eight = 4367 / 2225 := by
  norm_num [vLo, vHi, S, a, b, c, f]

theorem kernel_support (j : Kind) : Function.support (K j) ⊆ Icc (vLo j) (vHi j) := by
  intro v hv
  by_contra hn
  have he (t : ℝ) : masked j v t = 0 := if_neg (fun h => hn (slice_bounds h).1)
  exact hv (by rw [← slice_integral]; simp only [he, integral_zero])

theorem kernel_support_open (j : Kind) : Function.support (K j) ⊆ Ioo (1 : ℝ) 3 := by
  intro v hv
  have h := kernel_support j hv
  exact ⟨(image_constants j).1.trans_le h.1, h.2.trans_lt (image_constants j).2⟩

theorem endpoint_widths (j : Kind) : U j (vLo j) = L j (vLo j) ∧ U j (vHi j) = L j (vHi j) := by
  cases j <;> norm_num [U, L, vLo, vHi, invU, gamma5FeedbackW, gamma5ClassicalS, S, a, b, c, f]

theorem kernel_endpoints (j : Kind) : K j (vLo j) = 0 ∧ K j (vHi j) = 0 :=
  ⟨kernel_zero_width j (endpoint_widths j).1.le, kernel_zero_width j (endpoint_widths j).2.le⟩

theorem kernel_nonnegative (j : Kind) (v : ℝ) : 0 ≤ K j v := by
  rw [← slice_integral]
  exact integral_nonneg (fun t => (masked_bounds j v t).1)

theorem slice_denominators {j : Kind} {v t : ℝ} (h : slice j v t) :
    0 < v ∧ 0 < t ∧ 0 < invU j v t ∧ 0 < v * t * invU j v t := by
  have hv : 0 < v := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (slice_unit h).1
  have ht := constants.1.trans_le (slice_bounds h).2.1.1
  have hu := constants.1.trans_le (slice_bounds h).2.2.1
  exact ⟨hv, ht, hu, mul_pos (mul_pos hv ht) hu⟩

theorem source_denominators {j : Kind} {t u : ℝ} (h : region j t u) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧ 0 < t * u * (1 - t - u) := by
  have ht := constants.1.trans_le (region_bounds h).1.1
  have hu := constants.1.trans_le (region_bounds h).2.1.1
  have hz : 0 < 1 - t - u := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) (region_bounds h).2.2
  exact ⟨ht, hu, hz, mul_pos (mul_pos ht hu) hz⟩

theorem gamma6_log_denominator {v : ℝ} (hv : v ∈ Icc (1 : ℝ) 3) :
    0 < v * gamma5FeedbackW v := by
  have h0 : 0 < v := by linarith [hv.1]
  have hw : 0 < gamma5FeedbackW v := by
    norm_num [gamma5FeedbackW, gamma5ClassicalS]
    linarith [hv.2]
  exact mul_pos h0 hw

end Wu2008DoubleSieve.Gamma678Feedback
