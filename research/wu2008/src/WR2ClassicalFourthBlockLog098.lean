import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints098
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_098 (j : Fin 16) (hj : 16*98+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*98+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*98+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1568) ≤ val WuPaper.ClassicalFourthData.Bq 1568
    have hp : val WuPaper.ClassicalFourthData.Bq 1568 = (138269883742571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1568 = 138269883742571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1568 = (299:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1569) ≤ val WuPaper.ClassicalFourthData.Bq 1569
    have hp : val WuPaper.ClassicalFourthData.Bq 1569 = (138330502032665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1569 = 138330502032665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1569 = (9569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1570) ≤ val WuPaper.ClassicalFourthData.Bq 1570
    have hp : val WuPaper.ClassicalFourthData.Bq 1570 = (138391094177347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1570 = 138391094177347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1570 = (957:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1571) ≤ val WuPaper.ClassicalFourthData.Bq 1571
    have hp : val WuPaper.ClassicalFourthData.Bq 1571 = (138451660189652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1571 = 138451660189652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1571 = (9571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1572) ≤ val WuPaper.ClassicalFourthData.Bq 1572
    have hp : val WuPaper.ClassicalFourthData.Bq 1572 = (138512200082603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1572 = 138512200082603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1572 = (2393:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1573) ≤ val WuPaper.ClassicalFourthData.Bq 1573
    have hp : val WuPaper.ClassicalFourthData.Bq 1573 = (138572713869220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1573 = 138572713869220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1573 = (9573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1574) ≤ val WuPaper.ClassicalFourthData.Bq 1574
    have hp : val WuPaper.ClassicalFourthData.Bq 1574 = (138633201562510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1574 = 138633201562510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1574 = (4787:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1575) ≤ val WuPaper.ClassicalFourthData.Bq 1575
    have hp : val WuPaper.ClassicalFourthData.Bq 1575 = (138693663175475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1575 = 138693663175475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1575 = (383:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1575
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1576) ≤ val WuPaper.ClassicalFourthData.Bq 1576
    have hp : val WuPaper.ClassicalFourthData.Bq 1576 = (138754098721108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1576 = 138754098721108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1576 = (1197:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1577) ≤ val WuPaper.ClassicalFourthData.Bq 1577
    have hp : val WuPaper.ClassicalFourthData.Bq 1577 = (138814508212395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1577 = 138814508212395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1577 = (9577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1578) ≤ val WuPaper.ClassicalFourthData.Bq 1578
    have hp : val WuPaper.ClassicalFourthData.Bq 1578 = (138874891662313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1578 = 138874891662313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1578 = (4789:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1579) ≤ val WuPaper.ClassicalFourthData.Bq 1579
    have hp : val WuPaper.ClassicalFourthData.Bq 1579 = (138935249083830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1579 = 138935249083830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1579 = (9579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1580) ≤ val WuPaper.ClassicalFourthData.Bq 1580
    have hp : val WuPaper.ClassicalFourthData.Bq 1580 = (138995580489908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1580 = 138995580489908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1580 = (479:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1581) ≤ val WuPaper.ClassicalFourthData.Bq 1581
    have hp : val WuPaper.ClassicalFourthData.Bq 1581 = (139055885893501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1581 = 139055885893501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1581 = (9581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1582) ≤ val WuPaper.ClassicalFourthData.Bq 1582
    have hp : val WuPaper.ClassicalFourthData.Bq 1582 = (139116165307552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1582 = 139116165307552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1582 = (4791:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1583) ≤ val WuPaper.ClassicalFourthData.Bq 1583
    have hp : val WuPaper.ClassicalFourthData.Bq 1583 = (139176418745000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1583 = 139176418745000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1583 = (9583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_098
