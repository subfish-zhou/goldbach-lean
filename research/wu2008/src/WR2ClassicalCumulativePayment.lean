import WR2ClassicalCumulativeTable
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace WuPaper.ClassicalCumulativeTable

/-- The exact ceiling increment pays the rounded trapezoid and its error. -/
theorem increment_payment (q : ℕ → ℕ) (E i : ℕ) :
    3*4000^2*(q i+q (i+1))+E*1000000000000000 ≤
      6*4000^3*increment q E i := by
  unfold increment
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub]
  omega

/-- Every recursive step is paid without inspecting any concrete table entry. -/
theorem accumulate_payment (q : ℕ → ℕ) (E anchor start n : ℕ) :
    6*4000^3*accumulate q E anchor start n+
      3*4000^2*(q (start+n)+q (start+n+1))+E*1000000000000000 ≤
        6*4000^3*accumulate q E anchor start (n+1) := by
  rw [accumulate, Nat.mul_add]
  have h := increment_payment q E (start+n)
  omega

/-- Away from a block boundary, the reconstructed table takes one exact step. -/
theorem table_succ (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) :
    table q E anchor (i+1) = table q E anchor i+increment q E i := by
  have hi' : i+1 ≤ 10540 := by omega
  have hd : (i+1)/4 = i/4 := by omega
  have hm : (i+1)%4 = i%4+1 := by omega
  have he : 4*(i/4)+i%4 = i := by omega
  simp only [table, if_pos hi', if_pos hi.le, hd, hm, accumulate, he]

/-- Interior payments follow from the recurrence, not from finite table reduction. -/
theorem table_payment (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) :
    6*4000^3*table q E anchor i+
      3*4000^2*(q i+q (i+1))+E*1000000000000000 ≤
        6*4000^3*table q E anchor (i+1) := by
  rw [table_succ q E anchor hi hb, Nat.mul_add]
  have h := increment_payment q E i
  omega

end WuPaper.ClassicalCumulativeTable

#print axioms WuPaper.ClassicalCumulativeTable.increment_payment
#print axioms WuPaper.ClassicalCumulativeTable.accumulate_payment
#print axioms WuPaper.ClassicalCumulativeTable.table_succ
#print axioms WuPaper.ClassicalCumulativeTable.table_payment
