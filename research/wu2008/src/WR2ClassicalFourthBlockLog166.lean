import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints166
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_166 (j : Fin 16) (hj : 16*166+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*166+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*166+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2656) ≤ val WuPaper.ClassicalFourthData.Bq 2656
    have hp : val WuPaper.ClassicalFourthData.Bq 2656 = (191150278678310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2656 = 191150278678310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2656 = (333:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2657) ≤ val WuPaper.ClassicalFourthData.Bq 2657
    have hp : val WuPaper.ClassicalFourthData.Bq 2657 = (191188729097749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2657 = 191188729097749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2657 = (10657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2658) ≤ val WuPaper.ClassicalFourthData.Bq 2658
    have hp : val WuPaper.ClassicalFourthData.Bq 2658 = (191227163832968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2658 = 191227163832968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2658 = (5329:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2659) ≤ val WuPaper.ClassicalFourthData.Bq 2659
    have hp : val WuPaper.ClassicalFourthData.Bq 2659 = (191265582890926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2659 = 191265582890926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2659 = (10659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2660) ≤ val WuPaper.ClassicalFourthData.Bq 2660
    have hp : val WuPaper.ClassicalFourthData.Bq 2660 = (191303986278577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2660 = 191303986278577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2660 = (533:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2661) ≤ val WuPaper.ClassicalFourthData.Bq 2661
    have hp : val WuPaper.ClassicalFourthData.Bq 2661 = (191342374002871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2661 = 191342374002871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2661 = (10661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2662) ≤ val WuPaper.ClassicalFourthData.Bq 2662
    have hp : val WuPaper.ClassicalFourthData.Bq 2662 = (191380746070755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2662 = 191380746070755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2662 = (5331:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2663) ≤ val WuPaper.ClassicalFourthData.Bq 2663
    have hp : val WuPaper.ClassicalFourthData.Bq 2663 = (191419102489172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2663 = 191419102489172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2663 = (10663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2663
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2664) ≤ val WuPaper.ClassicalFourthData.Bq 2664
    have hp : val WuPaper.ClassicalFourthData.Bq 2664 = (191457443265061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2664 = 191457443265061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2664 = (1333:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2665) ≤ val WuPaper.ClassicalFourthData.Bq 2665
    have hp : val WuPaper.ClassicalFourthData.Bq 2665 = (191495768405357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2665 = 191495768405357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2665 = (2133:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2666) ≤ val WuPaper.ClassicalFourthData.Bq 2666
    have hp : val WuPaper.ClassicalFourthData.Bq 2666 = (191534077916992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2666 = 191534077916992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2666 = (5333:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2667) ≤ val WuPaper.ClassicalFourthData.Bq 2667
    have hp : val WuPaper.ClassicalFourthData.Bq 2667 = (191572371806894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2667 = 191572371806894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2667 = (10667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2668) ≤ val WuPaper.ClassicalFourthData.Bq 2668
    have hp : val WuPaper.ClassicalFourthData.Bq 2668 = (191610650081987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2668 = 191610650081987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2668 = (2667:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2669) ≤ val WuPaper.ClassicalFourthData.Bq 2669
    have hp : val WuPaper.ClassicalFourthData.Bq 2669 = (191648912749191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2669 = 191648912749191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2669 = (10669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2670) ≤ val WuPaper.ClassicalFourthData.Bq 2670
    have hp : val WuPaper.ClassicalFourthData.Bq 2670 = (191687159815424:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2670 = 191687159815424 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2670 = (1067:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2671) ≤ val WuPaper.ClassicalFourthData.Bq 2671
    have hp : val WuPaper.ClassicalFourthData.Bq 2671 = (191725391287598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2671 = 191725391287598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2671 = (10671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_166
