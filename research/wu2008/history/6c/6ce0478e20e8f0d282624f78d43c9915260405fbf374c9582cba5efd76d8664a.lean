import F1NextLedger
import TailWholeRationalPart

noncomputable section
namespace WuTarget.W10

theorem root_bounds :
    (77459666924148337703 : ℝ) / 10000000000000000000 ≤ F1JointFTC.root ∧
    F1JointFTC.root ≤ (77459666924148337704 : ℝ) / 10000000000000000000 := by
  constructor <;> nlinarith only [F1JointFTC.root_sq, F1JointFTC.root_pos]

theorem box_add {x y a b c d l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : l ≤ a + c) (hu : b + d ≤ u) :
    l ≤ x + y ∧ x + y ≤ u :=
  ⟨hl.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hu⟩

theorem box_sub {x y a b c d l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : l ≤ a - d) (hu : b - c ≤ u) :
    l ≤ x - y ∧ x - y ≤ u :=
  ⟨hl.trans (sub_le_sub hx.1 hy.2), (sub_le_sub hx.2 hy.1).trans hu⟩

theorem box_neg {x a b l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hl : l ≤ -b) (hu : -a ≤ u) : l ≤ -x ∧ -x ≤ u :=
  ⟨hl.trans (neg_le_neg hx.2), (neg_le_neg hx.1).trans hu⟩

theorem mul_upper {x y a b c d u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : a*c ≤ u) (had : a*d ≤ u) (hbc : b*c ≤ u) (hbd : b*d ≤ u) :
    x*y ≤ u := by
  by_cases h : 0 ≤ x
  · apply (mul_le_mul_of_nonneg_left hy.2 h).trans
    by_cases hd : 0 ≤ d
    · exact (mul_le_mul_of_nonneg_right hx.2 hd).trans hbd
    · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd)).trans had
  · apply (mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge h)).trans
    by_cases hc : 0 ≤ c
    · exact (mul_le_mul_of_nonneg_right hx.2 hc).trans hbc
    · exact (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc)).trans hac

theorem box_mul {x y a b c d l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hl : l ≤ a*c ∧ l ≤ a*d ∧ l ≤ b*c ∧ l ≤ b*d)
    (hu : a*c ≤ u ∧ a*d ≤ u ∧ b*c ≤ u ∧ b*d ≤ u) :
    l ≤ x*y ∧ x*y ≤ u := by
  refine ⟨?_, mul_upper hx hy hu.1 hu.2.1 hu.2.2.1 hu.2.2.2⟩
  have h := mul_upper ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩ hy
    (u := -l)
    (by nlinarith only [hl.2.2.1])
    (by nlinarith only [hl.2.2.2])
    (by nlinarith only [hl.1])
    (by nlinarith only [hl.2.1])
  nlinarith only [h]

theorem box_inv {x a b l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (ha : 0 < a)
    (hl : l ≤ 1/b) (hu : 1/a ≤ u) :
    l ≤ 1/x ∧ 1/x ≤ u :=
  ⟨hl.trans (one_div_le_one_div_of_le (ha.trans_le hx.1) hx.2),
    (one_div_le_one_div_of_le ha hx.1).trans hu⟩

theorem box_pow {x a b l u : ℝ} (n : ℕ)
    (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ a^n) (hu : b^n ≤ u) :
    l ≤ x^n ∧ x^n ≤ u :=
  ⟨hl.trans (pow_le_pow_left₀ ha hx.1 n),
    (pow_le_pow_left₀ (ha.trans hx.1) hx.2 n).trans hu⟩

theorem paid_log_bounds {x : ℝ} (hx : 1 ≤ x) :
    F1JointSplit.splitLow x + ActualTailConsumption.splitFloor x ≤ Real.log x ∧
    Real.log x ≤ F1JointSplit.splitHigh x - CliF1AffinePaymentParent.splitPayment x := by
  constructor
  · linarith only [ActualTailConsumption.splitFloor_le_endpoint hx]
  · linarith only [CliF1AffinePaymentParent.splitPayment_le_error hx]

end WuTarget.W10
