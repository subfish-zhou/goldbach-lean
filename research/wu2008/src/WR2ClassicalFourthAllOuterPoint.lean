import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativeDivision
namespace WuPaper.ClassicalFourthConditions
/-- Every outer sample is paid by its defining ceiling; no pointwise checks are needed. -/
theorem all_OuterPoint (i : ℕ) (hi : i < 10541) : OuterPoint (i) := by
  have hi' : i ≤ 10540 := by omega
  have hd : 0 < (12000+i)*(5308000-200*(12000+i)) :=
    Nat.mul_pos (by omega) (by omega)
  unfold OuterPoint ClassicalFourthData.outerq tail
  rw [if_pos hi']
  exact ClassicalCumulativeDivision.ceilDiv_paid _ _ hd
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_OuterPoint
