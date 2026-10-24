import WR2XiRectangleLower

/-! Exact interval maxima for the quadratic denominator in Xi2. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set

def quadraticDenominator (S t : ℝ) : ℝ := t * (1 - t / S)

def quadraticDenominatorMax (S a b : ℝ) : ℝ :=
  if b ≤ S / 2 then quadraticDenominator S b
  else if S / 2 ≤ a then quadraticDenominator S a else S / 4

private theorem quadraticDenominator_eq {S : ℝ} (hS : 0 < S) (t : ℝ) :
    quadraticDenominator S t = t * (S - t) / S := by
  unfold quadraticDenominator
  field_simp

theorem quadraticDenominator_pos {S t : ℝ} (ht : 0 < t) (htS : t < S) :
    0 < quadraticDenominator S t := by
  unfold quadraticDenominator
  exact mul_pos ht (sub_pos.mpr ((div_lt_one (ht.trans htS)).mpr htS))

theorem quadraticDenominator_le_max {S a b t : ℝ} (hS : 0 < S)
    (ht : t ∈ Icc a b) : quadraticDenominator S t ≤ quadraticDenominatorMax S a b := by
  unfold quadraticDenominatorMax
  split_ifs with hb ha
  · rw [quadraticDenominator_eq hS, quadraticDenominator_eq hS]
    apply div_le_div_of_nonneg_right _ hS.le
    nlinarith [ht.2]
  · rw [quadraticDenominator_eq hS, quadraticDenominator_eq hS]
    apply div_le_div_of_nonneg_right _ hS.le
    nlinarith [ht.1]
  · rw [quadraticDenominator_eq hS]
    apply (div_le_iff₀ hS).mpr
    nlinarith [sq_nonneg (t - S / 2)]

/-- The complete denominator hypotheses for an interior original-kernel panel. -/
theorem quadraticDenominator_panel {S a b t : ℝ} (ha : 0 < a) (hb : b < S)
    (ht : t ∈ Icc a b) :
    0 < quadraticDenominator S t ∧
      quadraticDenominator S t ≤ quadraticDenominatorMax S a b := by
  have htp := ha.trans_le ht.1
  have htS := ht.2.trans_lt hb
  exact ⟨quadraticDenominator_pos htp htS,
    quadraticDenominator_le_max (htp.trans htS) ht⟩

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.quadraticDenominator_panel
