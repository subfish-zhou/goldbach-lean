import WR2XiLogRefinement

/-! Lower rectangle sums for the logarithmic pieces of the original Xi2 kernel. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory
open scoped Interval BigOperators

theorem cellLogLower_div_le {x y d D : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y)
    (hd : 0 < d) (hdD : d ≤ D) : cellLogLower x / D ≤ log y / d := by
  calc
    _ ≤ cellLogLower x / d := div_le_div_of_nonneg_left (cellLogLower_nonneg hx) hd hdD
    _ ≤ log y / d := div_le_div_of_nonneg_right
      ((cellLogLower_le_log hx).trans (log_le_log (by linarith) hxy)) hd.le

/-- One rectangle uses a lower logarithm argument and an upper positive denominator. -/
theorem logarithmic_rectangle_lower {a b x D : ℝ} {r d : ℝ → ℝ}
    (hab : a ≤ b) (hx : 1 ≤ x)
    (hi : IntervalIntegrable (fun t => log (r t) / d t) volume a b)
    (hr : ∀ t ∈ Icc a b, x ≤ r t)
    (hd : ∀ t ∈ Icc a b, 0 < d t ∧ d t ≤ D) :
    (b - a) * (cellLogLower x / D) ≤ ∫ t in a..b, log (r t) / d t := by
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := cellLogLower x / D)) hi
    (fun t ht => cellLogLower_div_le hx (hr t ht) (hd t ht).1 (hd t ht).2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

/-- Adjacent rectangle payments add without duplicating endpoints or losing a panel. -/
theorem rectangle_sum_lower {f : ℝ → ℝ} {a c : ℕ → ℝ} {n : ℕ}
    (ha : ∀ k < n, a k ≤ a (k + 1))
    (hi : ∀ k < n, IntervalIntegrable f volume (a k) (a (k + 1)))
    (hc : ∀ k < n, ∀ t ∈ Icc (a k) (a (k + 1)), c k ≤ f t) :
    (∑ k ∈ Finset.range n, (a (k + 1) - a k) * c k) ≤
      ∫ t in a 0..a n, f t := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_le_sum
  intro k hk
  have hkn := Finset.mem_range.mp hk
  have h := intervalIntegral.integral_mono_on (ha k hkn)
    (intervalIntegrable_const (c := c k)) (hi k hkn) (hc k hkn)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.logarithmic_rectangle_lower
#print axioms WuPaper.R2Xi.rectangle_sum_lower
