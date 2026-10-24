import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints479
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_479 (j : Fin 16) (hj : 16*479+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*479+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*479+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7664) ≤ val WuPaper.ClassicalFourthData.Bq 7664
    have hp : val WuPaper.ClassicalFourthData.Bq 7664 = (273292342734333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7664 = 273292342734333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7664 = (979:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7665) ≤ val WuPaper.ClassicalFourthData.Bq 7665
    have hp : val WuPaper.ClassicalFourthData.Bq 7665 = (273296787578612:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7665 = 273296787578612 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7665 = (3133:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7666) ≤ val WuPaper.ClassicalFourthData.Bq 7666
    have hp : val WuPaper.ClassicalFourthData.Bq 7666 = (273301229979011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7666 = 273301229979011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7666 = (7833:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7667) ≤ val WuPaper.ClassicalFourthData.Bq 7667
    have hp : val WuPaper.ClassicalFourthData.Bq 7667 = (273305669936318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7667 = 273305669936318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7667 = (15667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7668) ≤ val WuPaper.ClassicalFourthData.Bq 7668
    have hp : val WuPaper.ClassicalFourthData.Bq 7668 = (273310107451322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7668 = 273310107451322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7668 = (3917:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7669) ≤ val WuPaper.ClassicalFourthData.Bq 7669
    have hp : val WuPaper.ClassicalFourthData.Bq 7669 = (273314542524814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7669 = 273314542524814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7669 = (15669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7670) ≤ val WuPaper.ClassicalFourthData.Bq 7670
    have hp : val WuPaper.ClassicalFourthData.Bq 7670 = (273318975157581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7670 = 273318975157581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7670 = (1567:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7671) ≤ val WuPaper.ClassicalFourthData.Bq 7671
    have hp : val WuPaper.ClassicalFourthData.Bq 7671 = (273323405350413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7671 = 273323405350413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7671 = (15671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7671
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7672) ≤ val WuPaper.ClassicalFourthData.Bq 7672
    have hp : val WuPaper.ClassicalFourthData.Bq 7672 = (273327833104097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7672 = 273327833104097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7672 = (1959:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7673) ≤ val WuPaper.ClassicalFourthData.Bq 7673
    have hp : val WuPaper.ClassicalFourthData.Bq 7673 = (273332258419421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7673 = 273332258419421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7673 = (15673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7674) ≤ val WuPaper.ClassicalFourthData.Bq 7674
    have hp : val WuPaper.ClassicalFourthData.Bq 7674 = (273336681297173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7674 = 273336681297173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7674 = (7837:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7675) ≤ val WuPaper.ClassicalFourthData.Bq 7675
    have hp : val WuPaper.ClassicalFourthData.Bq 7675 = (273341101738140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7675 = 273341101738140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7675 = (627:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7676) ≤ val WuPaper.ClassicalFourthData.Bq 7676
    have hp : val WuPaper.ClassicalFourthData.Bq 7676 = (273345519743109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7676 = 273345519743109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7676 = (3919:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7677) ≤ val WuPaper.ClassicalFourthData.Bq 7677
    have hp : val WuPaper.ClassicalFourthData.Bq 7677 = (273349935312868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7677 = 273349935312868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7677 = (15677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7678) ≤ val WuPaper.ClassicalFourthData.Bq 7678
    have hp : val WuPaper.ClassicalFourthData.Bq 7678 = (273354348448202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7678 = 273354348448202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7678 = (7839:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7679) ≤ val WuPaper.ClassicalFourthData.Bq 7679
    have hp : val WuPaper.ClassicalFourthData.Bq 7679 = (273358759149898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7679 = 273358759149898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7679 = (15679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_479
