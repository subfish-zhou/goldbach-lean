import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints229
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_229 (j : Fin 16) (hj : 16*229+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*229+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*229+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3664) ≤ val WuPaper.ClassicalFourthData.Bq 3664
    have hp : val WuPaper.ClassicalFourthData.Bq 3664 = (222990287911067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3664 = 222990287911067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3664 = (729:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3665) ≤ val WuPaper.ClassicalFourthData.Bq 3665
    have hp : val WuPaper.ClassicalFourthData.Bq 3665 = (223015911257227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3665 = 223015911257227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3665 = (2333:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3666) ≤ val WuPaper.ClassicalFourthData.Bq 3666
    have hp : val WuPaper.ClassicalFourthData.Bq 3666 = (223041524374584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3666 = 223041524374584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3666 = (5833:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3667) ≤ val WuPaper.ClassicalFourthData.Bq 3667
    have hp : val WuPaper.ClassicalFourthData.Bq 3667 = (223067127267290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3667 = 223067127267290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3667 = (11667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3668) ≤ val WuPaper.ClassicalFourthData.Bq 3668
    have hp : val WuPaper.ClassicalFourthData.Bq 3668 = (223092719939496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3668 = 223092719939496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3668 = (2917:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3669) ≤ val WuPaper.ClassicalFourthData.Bq 3669
    have hp : val WuPaper.ClassicalFourthData.Bq 3669 = (223118302395349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3669 = 223118302395349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3669 = (11669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3670) ≤ val WuPaper.ClassicalFourthData.Bq 3670
    have hp : val WuPaper.ClassicalFourthData.Bq 3670 = (223143874638998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3670 = 223143874638998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3670 = (1167:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3671) ≤ val WuPaper.ClassicalFourthData.Bq 3671
    have hp : val WuPaper.ClassicalFourthData.Bq 3671 = (223169436674585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3671 = 223169436674585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3671 = (11671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3671
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3672) ≤ val WuPaper.ClassicalFourthData.Bq 3672
    have hp : val WuPaper.ClassicalFourthData.Bq 3672 = (223194988506254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3672 = 223194988506254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3672 = (1459:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3673) ≤ val WuPaper.ClassicalFourthData.Bq 3673
    have hp : val WuPaper.ClassicalFourthData.Bq 3673 = (223220530138144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3673 = 223220530138144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3673 = (11673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3674) ≤ val WuPaper.ClassicalFourthData.Bq 3674
    have hp : val WuPaper.ClassicalFourthData.Bq 3674 = (223246061574395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3674 = 223246061574395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3674 = (5837:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3675) ≤ val WuPaper.ClassicalFourthData.Bq 3675
    have hp : val WuPaper.ClassicalFourthData.Bq 3675 = (223271582819142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3675 = 223271582819142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3675 = (467:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3676) ≤ val WuPaper.ClassicalFourthData.Bq 3676
    have hp : val WuPaper.ClassicalFourthData.Bq 3676 = (223297093876521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3676 = 223297093876521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3676 = (2919:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3677) ≤ val WuPaper.ClassicalFourthData.Bq 3677
    have hp : val WuPaper.ClassicalFourthData.Bq 3677 = (223322594750663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3677 = 223322594750663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3677 = (11677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3678) ≤ val WuPaper.ClassicalFourthData.Bq 3678
    have hp : val WuPaper.ClassicalFourthData.Bq 3678 = (223348085445699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3678 = 223348085445699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3678 = (5839:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3679) ≤ val WuPaper.ClassicalFourthData.Bq 3679
    have hp : val WuPaper.ClassicalFourthData.Bq 3679 = (223373565965756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3679 = 223373565965756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3679 = (11679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_229
