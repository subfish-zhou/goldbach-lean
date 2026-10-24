import WR2XiKernelPanels

/-! Product logarithms are paid factor by factor to keep each rational bound sharp. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory
open scoped Interval BigOperators

def productLogLower {n : ℕ} (q : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∑ j, cellLogLower ((a + 1) / q j)

theorem productLogLower_nonneg {n : ℕ} {q : Fin n → ℝ} {a : ℝ}
    (hq : ∀ j, 0 < q j ∧ q j ≤ a + 1) : 0 ≤ productLogLower q a := by
  apply Finset.sum_nonneg
  intro j _
  exact cellLogLower_nonneg ((one_le_div (hq j).1).mpr (hq j).2)

theorem productLogLower_le {n : ℕ} {q : Fin n → ℝ} {a t : ℝ}
    (ha : 0 < a + 1) (hat : a ≤ t)
    (hq : ∀ j, 0 < q j ∧ q j ≤ a + 1) :
    productLogLower q a ≤ log ((t + 1) ^ n / ∏ j, q j) := by
  have he : (∏ j : Fin n, (t + 1) / q j) = (t + 1) ^ n / ∏ j, q j := by
    rw [Finset.prod_div_distrib]
    simp
  rw [← he, log_prod (fun j _ => div_ne_zero (by linarith) (hq j).1.ne')]
  apply Finset.sum_le_sum
  intro j _
  apply (cellLogLower_le_log ((one_le_div (hq j).1).mpr (hq j).2)).trans
  exact log_le_log (div_pos ha (hq j).1)
    (div_le_div_of_nonneg_right (by linarith) (hq j).1.le)

/-- Covers the five-factor terminal piece and the two-factor middle piece of Xi2. -/
theorem product_kernel_panel {n : ℕ} {q : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hq : ∀ j, 0 < q j ∧ q j ≤ a + 1)
    (hi : IntervalIntegrable
      (fun t => log ((t + 1) ^ n / ∏ j, q j) / t) volume a b) :
    (b - a) * (productLogLower q a / b) ≤
      ∫ t in a..b, log ((t + 1) ^ n / ∏ j, q j) / t := by
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      productLogLower q a / b ≤ log ((t + 1) ^ n / ∏ j, q j) / t := by
    have htp := ha.trans_le ht.1
    calc
      _ ≤ productLogLower q a / t :=
        div_le_div_of_nonneg_left (productLogLower_nonneg hq) htp ht.2
      _ ≤ _ := div_le_div_of_nonneg_right
        (productLogLower_le (by linarith) ht.1 hq) htp.le
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := productLogLower q a / b)) hi hpoint
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.product_kernel_panel
