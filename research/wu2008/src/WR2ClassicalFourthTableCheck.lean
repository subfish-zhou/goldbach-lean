import WR2ClassicalFourthConditions
import WR2ExactRationalLog

/-! One soundness proof for every entry of the unchanged fourth-slot table. -/

namespace WuPaper.ClassicalFourthTableCheck
open ExactRational

def splitUpper (t : ℚ) : ℚ :=
  (logHi ((1+(t-1))/2) + logHi (2*(t-1)/(1+(t-1))))/t

@[simp] theorem cast_splitUpper (t : ℚ) :
    (splitUpper t : ℝ) = ClassicalB.splitUpper (t : ℝ) := by
  simp [splitUpper, ClassicalB.splitUpper, ClassicalLogSplit.upper]

def logCondition (i : ℕ) : Prop :=
  splitUpper (2+(i:ℚ)/4000) ≤ (ClassicalFourthData.Bq i : ℚ)/1000000000000000

theorem logCondition_sound {i : ℕ} (h : logCondition i) :
    ClassicalB.splitUpper (ClassicalFourthRecurrence.node 2 i) ≤
      ClassicalFourthConditions.val ClassicalFourthData.Bq i := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ClassicalFourthRecurrence.node, ClassicalFourthConditions.val] using hh

end WuPaper.ClassicalFourthTableCheck
