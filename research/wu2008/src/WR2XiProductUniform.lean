import WR2XiProductPanels
import WR2XiUniformPanels

/-! Uniform rational-log payments for a complete original product-log piece. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory
open scoped Interval BigOperators

def productPanelPayment {n : ℕ} (q : Fin n → ℝ) (a b : ℝ) (N k : ℕ) : ℝ :=
  ((b - a) / N) * (productLogLower q (panelPoint a b N k) /
    (5 * panelPoint a b N (k + 1)))

theorem product_uniform_lower {n N : ℕ} {q : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (hq : ∀ j, 0 < q j ∧ q j ≤ a + 1)
    (hi : IntervalIntegrable
      (fun t => log ((t + 1)^n / ∏ j, q j) / (5*t)) volume a b) :
    (∑ k ∈ Finset.range N, productPanelPayment q a b N k) ≤
      ∫ t in a..b, log ((t + 1)^n / ∏ j, q j) / (5*t) := by
  apply uniform_rectangle_lower hab hN hi
  intro k _ t ht
  have hm := panelPoint_mono hab N
  have hap : a ≤ panelPoint a b N k := by
    simpa only [panelPoint_zero] using hm (Nat.zero_le k)
  have hp : 0 < panelPoint a b N k := ha.trans_le hap
  have htp : 0 < t := hp.trans_le ht.1
  have hqp : ∀ j, 0 < q j ∧ q j ≤ panelPoint a b N k + 1 := by
    intro j
    exact ⟨(hq j).1, (hq j).2.trans (by linarith)⟩
  calc
    _ ≤ productLogLower q (panelPoint a b N k) / (5*t) :=
      div_le_div_of_nonneg_left (productLogLower_nonneg hqp) (by positivity)
        (by linarith [ht.2])
    _ ≤ _ := div_le_div_of_nonneg_right
      (productLogLower_le (by linarith) ht.1 hqp) (by positivity)

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.product_uniform_lower
