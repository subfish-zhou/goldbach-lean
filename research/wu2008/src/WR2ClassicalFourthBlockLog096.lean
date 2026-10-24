import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints096
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_096 (j : Fin 16) (hj : 16*96+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*96+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*96+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1536) ≤ val WuPaper.ClassicalFourthData.Bq 1536
    have hp : val WuPaper.ClassicalFourthData.Bq 1536 = (136316215266560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1536 = 136316215266560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1536 = (298:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1537) ≤ val WuPaper.ClassicalFourthData.Bq 1537
    have hp : val WuPaper.ClassicalFourthData.Bq 1537 = (136377677139956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1537 = 136377677139956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1537 = (9537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1538) ≤ val WuPaper.ClassicalFourthData.Bq 1538
    have hp : val WuPaper.ClassicalFourthData.Bq 1538 = (136439112446584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1538 = 136439112446584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1538 = (4769:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1539) ≤ val WuPaper.ClassicalFourthData.Bq 1539
    have hp : val WuPaper.ClassicalFourthData.Bq 1539 = (136500521199739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1539 = 136500521199739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1539 = (9539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1540) ≤ val WuPaper.ClassicalFourthData.Bq 1540
    have hp : val WuPaper.ClassicalFourthData.Bq 1540 = (136561903412706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1540 = 136561903412706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1540 = (477:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1541) ≤ val WuPaper.ClassicalFourthData.Bq 1541
    have hp : val WuPaper.ClassicalFourthData.Bq 1541 = (136623259098762:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1541 = 136623259098762 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1541 = (9541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1542) ≤ val WuPaper.ClassicalFourthData.Bq 1542
    have hp : val WuPaper.ClassicalFourthData.Bq 1542 = (136684588271179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1542 = 136684588271179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1542 = (4771:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1543) ≤ val WuPaper.ClassicalFourthData.Bq 1543
    have hp : val WuPaper.ClassicalFourthData.Bq 1543 = (136745890943216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1543 = 136745890943216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1543 = (9543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1543
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1544) ≤ val WuPaper.ClassicalFourthData.Bq 1544
    have hp : val WuPaper.ClassicalFourthData.Bq 1544 = (136807167128128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1544 = 136807167128128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1544 = (1193:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1545) ≤ val WuPaper.ClassicalFourthData.Bq 1545
    have hp : val WuPaper.ClassicalFourthData.Bq 1545 = (136868416839158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1545 = 136868416839158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1545 = (1909:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1546) ≤ val WuPaper.ClassicalFourthData.Bq 1546
    have hp : val WuPaper.ClassicalFourthData.Bq 1546 = (136929640089544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1546 = 136929640089544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1546 = (4773:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1547) ≤ val WuPaper.ClassicalFourthData.Bq 1547
    have hp : val WuPaper.ClassicalFourthData.Bq 1547 = (136990836892514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1547 = 136990836892514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1547 = (9547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1548) ≤ val WuPaper.ClassicalFourthData.Bq 1548
    have hp : val WuPaper.ClassicalFourthData.Bq 1548 = (137052007261289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1548 = 137052007261289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1548 = (2387:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1549) ≤ val WuPaper.ClassicalFourthData.Bq 1549
    have hp : val WuPaper.ClassicalFourthData.Bq 1549 = (137113151209079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1549 = 137113151209079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1549 = (9549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1550) ≤ val WuPaper.ClassicalFourthData.Bq 1550
    have hp : val WuPaper.ClassicalFourthData.Bq 1550 = (137174268749091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1550 = 137174268749091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1550 = (191:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1551) ≤ val WuPaper.ClassicalFourthData.Bq 1551
    have hp : val WuPaper.ClassicalFourthData.Bq 1551 = (137235359894518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1551 = 137235359894518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1551 = (9551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1551
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_096
