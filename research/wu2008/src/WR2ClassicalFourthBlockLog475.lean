import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints475
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_475 (j : Fin 16) (hj : 16*475+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*475+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*475+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7600) ≤ val WuPaper.ClassicalFourthData.Bq 7600
    have hp : val WuPaper.ClassicalFourthData.Bq 7600 = (273002753075256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7600 = 273002753075256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7600 = (39:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7601) ≤ val WuPaper.ClassicalFourthData.Bq 7601
    have hp : val WuPaper.ClassicalFourthData.Bq 7601 = (273007355983450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7601 = 273007355983450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7601 = (15601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7602) ≤ val WuPaper.ClassicalFourthData.Bq 7602
    have hp : val WuPaper.ClassicalFourthData.Bq 7602 = (273011956396630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7602 = 273011956396630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7602 = (7801:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7603) ≤ val WuPaper.ClassicalFourthData.Bq 7603
    have hp : val WuPaper.ClassicalFourthData.Bq 7603 = (273016554315605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7603 = 273016554315605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7603 = (15603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7604) ≤ val WuPaper.ClassicalFourthData.Bq 7604
    have hp : val WuPaper.ClassicalFourthData.Bq 7604 = (273021149741181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7604 = 273021149741181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7604 = (3901:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7605) ≤ val WuPaper.ClassicalFourthData.Bq 7605
    have hp : val WuPaper.ClassicalFourthData.Bq 7605 = (273025742674166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7605 = 273025742674166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7605 = (3121:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7606) ≤ val WuPaper.ClassicalFourthData.Bq 7606
    have hp : val WuPaper.ClassicalFourthData.Bq 7606 = (273030333115369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7606 = 273030333115369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7606 = (7803:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7607) ≤ val WuPaper.ClassicalFourthData.Bq 7607
    have hp : val WuPaper.ClassicalFourthData.Bq 7607 = (273034921065594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7607 = 273034921065594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7607 = (15607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7607
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7608) ≤ val WuPaper.ClassicalFourthData.Bq 7608
    have hp : val WuPaper.ClassicalFourthData.Bq 7608 = (273039506525650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7608 = 273039506525650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7608 = (1951:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7609) ≤ val WuPaper.ClassicalFourthData.Bq 7609
    have hp : val WuPaper.ClassicalFourthData.Bq 7609 = (273044089496342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7609 = 273044089496342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7609 = (15609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7610) ≤ val WuPaper.ClassicalFourthData.Bq 7610
    have hp : val WuPaper.ClassicalFourthData.Bq 7610 = (273048669978476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7610 = 273048669978476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7610 = (1561:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7611) ≤ val WuPaper.ClassicalFourthData.Bq 7611
    have hp : val WuPaper.ClassicalFourthData.Bq 7611 = (273053247972859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7611 = 273053247972859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7611 = (15611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7612) ≤ val WuPaper.ClassicalFourthData.Bq 7612
    have hp : val WuPaper.ClassicalFourthData.Bq 7612 = (273057823480295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7612 = 273057823480295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7612 = (3903:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7613) ≤ val WuPaper.ClassicalFourthData.Bq 7613
    have hp : val WuPaper.ClassicalFourthData.Bq 7613 = (273062396501590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7613 = 273062396501590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7613 = (15613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7614) ≤ val WuPaper.ClassicalFourthData.Bq 7614
    have hp : val WuPaper.ClassicalFourthData.Bq 7614 = (273066967037549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7614 = 273066967037549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7614 = (7807:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7615) ≤ val WuPaper.ClassicalFourthData.Bq 7615
    have hp : val WuPaper.ClassicalFourthData.Bq 7615 = (273071535088976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7615 = 273071535088976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7615 = (3123:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_475
