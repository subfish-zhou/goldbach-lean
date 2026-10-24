import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints161
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_161 (j : Fin 16) (hj : 16*161+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*161+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*161+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2576) ≤ val WuPaper.ClassicalFourthData.Bq 2576
    have hp : val WuPaper.ClassicalFourthData.Bq 2576 = (188022805080934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2576 = 188022805080934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2576 = (661:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2577) ≤ val WuPaper.ClassicalFourthData.Bq 2577
    have hp : val WuPaper.ClassicalFourthData.Bq 2577 = (188062533118776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2577 = 188062533118776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2577 = (10577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2578) ≤ val WuPaper.ClassicalFourthData.Bq 2578
    have hp : val WuPaper.ClassicalFourthData.Bq 2578 = (188102244903375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2578 = 188102244903375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2578 = (5289:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2579) ≤ val WuPaper.ClassicalFourthData.Bq 2579
    have hp : val WuPaper.ClassicalFourthData.Bq 2579 = (188141940441997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2579 = 188141940441997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2579 = (10579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2580) ≤ val WuPaper.ClassicalFourthData.Bq 2580
    have hp : val WuPaper.ClassicalFourthData.Bq 2580 = (188181619741904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2580 = 188181619741904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2580 = (529:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2581) ≤ val WuPaper.ClassicalFourthData.Bq 2581
    have hp : val WuPaper.ClassicalFourthData.Bq 2581 = (188221282810355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2581 = 188221282810355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2581 = (10581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2582) ≤ val WuPaper.ClassicalFourthData.Bq 2582
    have hp : val WuPaper.ClassicalFourthData.Bq 2582 = (188260929654606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2582 = 188260929654606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2582 = (5291:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2583) ≤ val WuPaper.ClassicalFourthData.Bq 2583
    have hp : val WuPaper.ClassicalFourthData.Bq 2583 = (188300560281905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2583 = 188300560281905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2583 = (10583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2583
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2584) ≤ val WuPaper.ClassicalFourthData.Bq 2584
    have hp : val WuPaper.ClassicalFourthData.Bq 2584 = (188340174699501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2584 = 188340174699501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2584 = (1323:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2585) ≤ val WuPaper.ClassicalFourthData.Bq 2585
    have hp : val WuPaper.ClassicalFourthData.Bq 2585 = (188379772914636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2585 = 188379772914636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2585 = (2117:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2586) ≤ val WuPaper.ClassicalFourthData.Bq 2586
    have hp : val WuPaper.ClassicalFourthData.Bq 2586 = (188419354934549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2586 = 188419354934549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2586 = (5293:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2587) ≤ val WuPaper.ClassicalFourthData.Bq 2587
    have hp : val WuPaper.ClassicalFourthData.Bq 2587 = (188458920766475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2587 = 188458920766475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2587 = (10587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2588) ≤ val WuPaper.ClassicalFourthData.Bq 2588
    have hp : val WuPaper.ClassicalFourthData.Bq 2588 = (188498470417644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2588 = 188498470417644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2588 = (2647:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2589) ≤ val WuPaper.ClassicalFourthData.Bq 2589
    have hp : val WuPaper.ClassicalFourthData.Bq 2589 = (188538003895285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2589 = 188538003895285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2589 = (10589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2590) ≤ val WuPaper.ClassicalFourthData.Bq 2590
    have hp : val WuPaper.ClassicalFourthData.Bq 2590 = (188577521206620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2590 = 188577521206620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2590 = (1059:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2591) ≤ val WuPaper.ClassicalFourthData.Bq 2591
    have hp : val WuPaper.ClassicalFourthData.Bq 2591 = (188617022358868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2591 = 188617022358868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2591 = (10591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_161
