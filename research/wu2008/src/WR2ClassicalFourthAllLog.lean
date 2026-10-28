import WR2ClassicalFourthTableCheck
import WR2ClassicalFourthBqSoundness
namespace WuPaper.ClassicalFourthConditions
theorem all_Log (i : ℕ) (hi : i < 10541) : WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (i)) ≤ val WuPaper.ClassicalFourthData.Bq (i) := by
  apply ClassicalFourthTableCheck.logCondition_sound
  exact FourthBqInteger.Bq_paid (by omega)
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_Log
