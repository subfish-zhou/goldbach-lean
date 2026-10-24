import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints410
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_410 (j : Fin 16) (hj : 16*410+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*410+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*410+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6560) ≤ val WuPaper.ClassicalFourthData.Bq 6560
    have hp : val WuPaper.ClassicalFourthData.Bq 6560 = (266697504713821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6560 = 266697504713821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6560 = (91:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6561) ≤ val WuPaper.ClassicalFourthData.Bq 6561
    have hp : val WuPaper.ClassicalFourthData.Bq 6561 = (266705201468177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6561 = 266705201468177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6561 = (14561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6562) ≤ val WuPaper.ClassicalFourthData.Bq 6562
    have hp : val WuPaper.ClassicalFourthData.Bq 6562 = (266712894702633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6562 = 266712894702633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6562 = (7281:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6563) ≤ val WuPaper.ClassicalFourthData.Bq 6563
    have hp : val WuPaper.ClassicalFourthData.Bq 6563 = (266720584418380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6563 = 266720584418380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6563 = (14563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6564) ≤ val WuPaper.ClassicalFourthData.Bq 6564
    have hp : val WuPaper.ClassicalFourthData.Bq 6564 = (266728270616611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6564 = 266728270616611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6564 = (3641:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6565) ≤ val WuPaper.ClassicalFourthData.Bq 6565
    have hp : val WuPaper.ClassicalFourthData.Bq 6565 = (266735953298514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6565 = 266735953298514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6565 = (2913:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6566) ≤ val WuPaper.ClassicalFourthData.Bq 6566
    have hp : val WuPaper.ClassicalFourthData.Bq 6566 = (266743632465280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6566 = 266743632465280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6566 = (7283:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6567) ≤ val WuPaper.ClassicalFourthData.Bq 6567
    have hp : val WuPaper.ClassicalFourthData.Bq 6567 = (266751308118099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6567 = 266751308118099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6567 = (14567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6567
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6568) ≤ val WuPaper.ClassicalFourthData.Bq 6568
    have hp : val WuPaper.ClassicalFourthData.Bq 6568 = (266758980258160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6568 = 266758980258160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6568 = (1821:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6569) ≤ val WuPaper.ClassicalFourthData.Bq 6569
    have hp : val WuPaper.ClassicalFourthData.Bq 6569 = (266766648886651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6569 = 266766648886651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6569 = (14569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6570) ≤ val WuPaper.ClassicalFourthData.Bq 6570
    have hp : val WuPaper.ClassicalFourthData.Bq 6570 = (266774314004761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6570 = 266774314004761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6570 = (1457:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6571) ≤ val WuPaper.ClassicalFourthData.Bq 6571
    have hp : val WuPaper.ClassicalFourthData.Bq 6571 = (266781975613677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6571 = 266781975613677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6571 = (14571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6572) ≤ val WuPaper.ClassicalFourthData.Bq 6572
    have hp : val WuPaper.ClassicalFourthData.Bq 6572 = (266789633714586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6572 = 266789633714586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6572 = (3643:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6573) ≤ val WuPaper.ClassicalFourthData.Bq 6573
    have hp : val WuPaper.ClassicalFourthData.Bq 6573 = (266797288308676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6573 = 266797288308676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6573 = (14573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6574) ≤ val WuPaper.ClassicalFourthData.Bq 6574
    have hp : val WuPaper.ClassicalFourthData.Bq 6574 = (266804939397133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6574 = 266804939397133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6574 = (7287:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6575) ≤ val WuPaper.ClassicalFourthData.Bq 6575
    have hp : val WuPaper.ClassicalFourthData.Bq 6575 = (266812586981142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6575 = 266812586981142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6575 = (583:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_410
