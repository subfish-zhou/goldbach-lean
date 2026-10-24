import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints543
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_543 (j : Fin 16) (hj : 16*543+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*543+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*543+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8688) ≤ val WuPaper.ClassicalFourthData.Bq 8688
    have hp : val WuPaper.ClassicalFourthData.Bq 8688 = (276692786141573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8688 = 276692786141573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8688 = (1043:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8689) ≤ val WuPaper.ClassicalFourthData.Bq 8689
    have hp : val WuPaper.ClassicalFourthData.Bq 8689 = (276695096244220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8689 = 276695096244220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8689 = (16689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8690) ≤ val WuPaper.ClassicalFourthData.Bq 8690
    have hp : val WuPaper.ClassicalFourthData.Bq 8690 = (276697404581543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8690 = 276697404581543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8690 = (1669:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8691) ≤ val WuPaper.ClassicalFourthData.Bq 8691
    have hp : val WuPaper.ClassicalFourthData.Bq 8691 = (276699711154092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8691 = 276699711154092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8691 = (16691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8692) ≤ val WuPaper.ClassicalFourthData.Bq 8692
    have hp : val WuPaper.ClassicalFourthData.Bq 8692 = (276702015962420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8692 = 276702015962420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8692 = (4173:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8693) ≤ val WuPaper.ClassicalFourthData.Bq 8693
    have hp : val WuPaper.ClassicalFourthData.Bq 8693 = (276704319007078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8693 = 276704319007078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8693 = (16693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8694) ≤ val WuPaper.ClassicalFourthData.Bq 8694
    have hp : val WuPaper.ClassicalFourthData.Bq 8694 = (276706620288617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8694 = 276706620288617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8694 = (8347:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8695) ≤ val WuPaper.ClassicalFourthData.Bq 8695
    have hp : val WuPaper.ClassicalFourthData.Bq 8695 = (276708919807590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8695 = 276708919807590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8695 = (3339:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8695
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8696) ≤ val WuPaper.ClassicalFourthData.Bq 8696
    have hp : val WuPaper.ClassicalFourthData.Bq 8696 = (276711217564545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8696 = 276711217564545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8696 = (2087:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8697) ≤ val WuPaper.ClassicalFourthData.Bq 8697
    have hp : val WuPaper.ClassicalFourthData.Bq 8697 = (276713513560035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8697 = 276713513560035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8697 = (16697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8698) ≤ val WuPaper.ClassicalFourthData.Bq 8698
    have hp : val WuPaper.ClassicalFourthData.Bq 8698 = (276715807794610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8698 = 276715807794610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8698 = (8349:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8699) ≤ val WuPaper.ClassicalFourthData.Bq 8699
    have hp : val WuPaper.ClassicalFourthData.Bq 8699 = (276718100268821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8699 = 276718100268821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8699 = (16699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8700) ≤ val WuPaper.ClassicalFourthData.Bq 8700
    have hp : val WuPaper.ClassicalFourthData.Bq 8700 = (276720390983216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8700 = 276720390983216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8700 = (167:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8701) ≤ val WuPaper.ClassicalFourthData.Bq 8701
    have hp : val WuPaper.ClassicalFourthData.Bq 8701 = (276722679938347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8701 = 276722679938347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8701 = (16701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8702) ≤ val WuPaper.ClassicalFourthData.Bq 8702
    have hp : val WuPaper.ClassicalFourthData.Bq 8702 = (276724967134763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8702 = 276724967134763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8702 = (8351:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8703) ≤ val WuPaper.ClassicalFourthData.Bq 8703
    have hp : val WuPaper.ClassicalFourthData.Bq 8703 = (276727252573014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8703 = 276727252573014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8703 = (16703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_543
