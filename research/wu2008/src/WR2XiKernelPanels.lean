import WR2XiArgumentBounds

/-! Integral payments for the original tail and mixed Xi2 kernel pieces. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory
open scoped Interval

/-- A complete panel of either original J-tail logarithmic kernel. -/
theorem tail_kernel_panel {S k a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S - 1) (hk : 1 < k)
    (hx : 1 ≤ (a + 1) / ((k - 1) * (S - 1 - a)))
    (hi : IntervalIntegrable
      (fun t => log ((t + 1) / ((k - 1) * (S - 1 - t))) / t) volume a b) :
    (b - a) * (cellLogLower ((a + 1) / ((k - 1) * (S - 1 - a))) / b) ≤
      ∫ t in a..b, log ((t + 1) / ((k - 1) * (S - 1 - t))) / t := by
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    exact tail_argument_mono (by linarith) hk ht.1 (ht.2.trans_lt hb)
  · intro t ht
    exact ⟨ha.trans_le ht.1, ht.2⟩

/-- A complete panel of the middle gamma-six logarithmic kernel. -/
theorem mixed_kernel_panel {S k a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S) (hk : 0 ≤ k) (hkS : k ≤ S)
    (hbD : 0 < k * S - S - k * b)
    (hx : 1 ≤ S * (S - 1 - a) / (k * S - S - k * a))
    (hi : IntervalIntegrable
      (fun t => log (S * (S - 1 - t) / (k * S - S - k * t)) /
        quadraticDenominator S t) volume a b) :
    (b - a) * (cellLogLower (S * (S - 1 - a) / (k * S - S - k * a)) /
      quadraticDenominatorMax S a b) ≤
      ∫ t in a..b, log (S * (S - 1 - t) / (k * S - S - k * t)) /
        quadraticDenominator S t := by
  have hD (t : ℝ) (ht : t ≤ b) : 0 < k * S - S - k * t := by
    nlinarith [mul_nonneg hk (sub_nonneg.mpr ht)]
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    exact mixed_argument_mono ((ha.trans_le hab).trans hb) hkS ht.1
      (hD a hab) (hD t ht.2)
  · intro t ht
    exact quadraticDenominator_panel ha hb ht

/-- A complete panel of the triangular mother-region logarithmic kernel. -/
theorem triangular_kernel_panel {S k a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S) (hk : 0 ≤ k) (hbD : 0 < k * S - S - k * b)
    (hx : 1 ≤ S / (k * S - S - k * a))
    (hi : IntervalIntegrable
      (fun t => log (S / (k * S - S - k * t)) / quadraticDenominator S t) volume a b) :
    (b - a) * (cellLogLower (S / (k * S - S - k * a)) /
      quadraticDenominatorMax S a b) ≤
      ∫ t in a..b, log (S / (k * S - S - k * t)) / quadraticDenominator S t := by
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    apply triangular_argument_mono ((ha.trans_le hab).trans hb).le hk ht.1
    nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.2)]
  · intro t ht
    exact quadraticDenominator_panel ha hb ht

/-- A complete panel of the final decreasing logarithmic kernel. -/
theorem final_kernel_panel {S a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S) (hx : 1 ≤ S - 1 - b)
    (hi : IntervalIntegrable
      (fun t => log (S - 1 - t) / quadraticDenominator S t) volume a b) :
    (b - a) * (cellLogLower (S - 1 - b) / quadraticDenominatorMax S a b) ≤
      ∫ t in a..b, log (S - 1 - t) / quadraticDenominator S t := by
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    exact final_argument_lower ht.2
  · intro t ht
    exact quadraticDenominator_panel ha hb ht

/-- A complete panel of the rectangular mother-region logarithmic kernel. -/
theorem rectangular_kernel_panel {S k l a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < S) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hkD : 0 < k * S - S - k * b) (hlD : 0 < l * S - S - l * b)
    (hx : 1 ≤ S ^ 2 / ((k * S - S - k * a) * (l * S - S - l * a)))
    (hi : IntervalIntegrable
      (fun t => log (S ^ 2 / ((k * S - S - k * t) * (l * S - S - l * t))) /
        quadraticDenominator S t) volume a b) :
    (b - a) * (cellLogLower (S ^ 2 / ((k * S - S - k * a) * (l * S - S - l * a))) /
      quadraticDenominatorMax S a b) ≤
      ∫ t in a..b, log (S ^ 2 / ((k * S - S - k * t) * (l * S - S - l * t))) /
        quadraticDenominator S t := by
  apply logarithmic_rectangle_lower hab hx hi
  · intro t ht
    apply reciprocal_product_le (sq_nonneg S)
    · nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.1)]
    · nlinarith [mul_nonneg hl (sub_nonneg.mpr ht.1)]
    · nlinarith [mul_nonneg hk (sub_nonneg.mpr ht.2)]
    · nlinarith [mul_nonneg hl (sub_nonneg.mpr ht.2)]
  · intro t ht
    exact quadraticDenominator_panel ha hb ht

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.tail_kernel_panel
#print axioms WuPaper.R2Xi.mixed_kernel_panel

#print axioms WuPaper.R2Xi.triangular_kernel_panel
#print axioms WuPaper.R2Xi.final_kernel_panel
#print axioms WuPaper.R2Xi.rectangular_kernel_panel
