import WR2XiKernelPanels

/-! Rectangle payments with the original factor five retained in the denominator. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory
open scoped Interval

theorem scaled_tail_kernel_panel {S k a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S - 1) (hk : 1 < k)
    (hx : 1 ≤ (a + 1) / ((k - 1) * (S - 1 - a)))
    (hi : IntervalIntegrable
      (fun t => log ((t + 1) / ((k - 1) * (S - 1 - t))) / (5*t)) volume a b) :
    (b-a) * (cellLogLower ((a+1)/((k-1)*(S-1-a))) / (5*b)) ≤
      ∫ t in a..b, log ((t+1)/((k-1)*(S-1-t))) / (5*t) := by
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    exact tail_argument_mono (by linarith) hk ht.1 (ht.2.trans_lt hb)
  · intro t ht
    constructor <;> linarith [ht.1, ht.2]

/-- Common quadratic denominator comparison for all four mother-region pieces. -/
theorem scaled_quadratic_rectangle {S a b x : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < S) (hx : 1 ≤ x)
    (hi : IntervalIntegrable (fun t => log (f t) / (5*t*(1-t/S))) volume a b)
    (hf : ∀ t ∈ Icc a b, x ≤ f t) :
    (b-a) * (cellLogLower x / (5*quadraticDenominatorMax S a b)) ≤
      ∫ t in a..b, log (f t) / (5*t*(1-t/S)) := by
  apply logarithmic_rectangle_lower hab hx hi hf
  intro t ht
  have h := quadraticDenominator_panel ha hb ht
  unfold quadraticDenominator at h
  constructor <;> nlinarith [h.1, h.2]

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.scaled_tail_kernel_panel
#print axioms WuPaper.R2Xi.scaled_quadratic_rectangle
