import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints598
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_598 (j : Fin 16) (hj : 16*598+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*598+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*598+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9568) ≤ val WuPaper.ClassicalFourthData.Bq 9568
    have hp : val WuPaper.ClassicalFourthData.Bq 9568 = (278101028683335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9568 = 278101028683335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9568 = (549:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9569) ≤ val WuPaper.ClassicalFourthData.Bq 9569
    have hp : val WuPaper.ClassicalFourthData.Bq 9569 = (278101979188697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9569 = 278101979188697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9569 = (17569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9570) ≤ val WuPaper.ClassicalFourthData.Bq 9570
    have hp : val WuPaper.ClassicalFourthData.Bq 9570 = (278102928349367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9570 = 278102928349367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9570 = (1757:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9571) ≤ val WuPaper.ClassicalFourthData.Bq 9571
    have hp : val WuPaper.ClassicalFourthData.Bq 9571 = (278103876165758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9571 = 278103876165758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9571 = (17571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9572) ≤ val WuPaper.ClassicalFourthData.Bq 9572
    have hp : val WuPaper.ClassicalFourthData.Bq 9572 = (278104822638279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9572 = 278104822638279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9572 = (4393:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9573) ≤ val WuPaper.ClassicalFourthData.Bq 9573
    have hp : val WuPaper.ClassicalFourthData.Bq 9573 = (278105767767344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9573 = 278105767767344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9573 = (17573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9574) ≤ val WuPaper.ClassicalFourthData.Bq 9574
    have hp : val WuPaper.ClassicalFourthData.Bq 9574 = (278106711553363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9574 = 278106711553363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9574 = (8787:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9575) ≤ val WuPaper.ClassicalFourthData.Bq 9575
    have hp : val WuPaper.ClassicalFourthData.Bq 9575 = (278107653996749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9575 = 278107653996749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9575 = (703:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9575
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9576) ≤ val WuPaper.ClassicalFourthData.Bq 9576
    have hp : val WuPaper.ClassicalFourthData.Bq 9576 = (278108595097911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9576 = 278108595097911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9576 = (2197:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9577) ≤ val WuPaper.ClassicalFourthData.Bq 9577
    have hp : val WuPaper.ClassicalFourthData.Bq 9577 = (278109534857261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9577 = 278109534857261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9577 = (17577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9578) ≤ val WuPaper.ClassicalFourthData.Bq 9578
    have hp : val WuPaper.ClassicalFourthData.Bq 9578 = (278110473275210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9578 = 278110473275210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9578 = (8789:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9579) ≤ val WuPaper.ClassicalFourthData.Bq 9579
    have hp : val WuPaper.ClassicalFourthData.Bq 9579 = (278111410352168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9579 = 278111410352168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9579 = (17579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9580) ≤ val WuPaper.ClassicalFourthData.Bq 9580
    have hp : val WuPaper.ClassicalFourthData.Bq 9580 = (278112346088547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9580 = 278112346088547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9580 = (879:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9581) ≤ val WuPaper.ClassicalFourthData.Bq 9581
    have hp : val WuPaper.ClassicalFourthData.Bq 9581 = (278113280484757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9581 = 278113280484757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9581 = (17581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9582) ≤ val WuPaper.ClassicalFourthData.Bq 9582
    have hp : val WuPaper.ClassicalFourthData.Bq 9582 = (278114213541207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9582 = 278114213541207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9582 = (8791:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9583) ≤ val WuPaper.ClassicalFourthData.Bq 9583
    have hp : val WuPaper.ClassicalFourthData.Bq 9583 = (278115145258309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9583 = 278115145258309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9583 = (17583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_598
