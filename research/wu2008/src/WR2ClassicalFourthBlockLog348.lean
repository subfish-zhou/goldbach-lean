import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints348
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_348 (j : Fin 16) (hj : 16*348+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*348+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*348+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5568) ≤ val WuPaper.ClassicalFourthData.Bq 5568
    have hp : val WuPaper.ClassicalFourthData.Bq 5568 = (257113748846813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5568 = 257113748846813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5568 = (424:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5569) ≤ val WuPaper.ClassicalFourthData.Bq 5569
    have hp : val WuPaper.ClassicalFourthData.Bq 5569 = (257125608571668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5569 = 257125608571668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5569 = (13569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5570) ≤ val WuPaper.ClassicalFourthData.Bq 5570
    have hp : val WuPaper.ClassicalFourthData.Bq 5570 = (257137463329397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5570 = 257137463329397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5570 = (1357:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5571) ≤ val WuPaper.ClassicalFourthData.Bq 5571
    have hp : val WuPaper.ClassicalFourthData.Bq 5571 = (257149313121770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5571 = 257149313121770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5571 = (13571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5572) ≤ val WuPaper.ClassicalFourthData.Bq 5572
    have hp : val WuPaper.ClassicalFourthData.Bq 5572 = (257161157950558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5572 = 257161157950558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5572 = (3393:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5573) ≤ val WuPaper.ClassicalFourthData.Bq 5573
    have hp : val WuPaper.ClassicalFourthData.Bq 5573 = (257172997817529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5573 = 257172997817529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5573 = (13573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5574) ≤ val WuPaper.ClassicalFourthData.Bq 5574
    have hp : val WuPaper.ClassicalFourthData.Bq 5574 = (257184832724453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5574 = 257184832724453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5574 = (6787:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5575) ≤ val WuPaper.ClassicalFourthData.Bq 5575
    have hp : val WuPaper.ClassicalFourthData.Bq 5575 = (257196662673098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5575 = 257196662673098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5575 = (543:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5575
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5576) ≤ val WuPaper.ClassicalFourthData.Bq 5576
    have hp : val WuPaper.ClassicalFourthData.Bq 5576 = (257208487665229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5576 = 257208487665229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5576 = (1697:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5577) ≤ val WuPaper.ClassicalFourthData.Bq 5577
    have hp : val WuPaper.ClassicalFourthData.Bq 5577 = (257220307702614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5577 = 257220307702614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5577 = (13577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5578) ≤ val WuPaper.ClassicalFourthData.Bq 5578
    have hp : val WuPaper.ClassicalFourthData.Bq 5578 = (257232122787018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5578 = 257232122787018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5578 = (6789:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5579) ≤ val WuPaper.ClassicalFourthData.Bq 5579
    have hp : val WuPaper.ClassicalFourthData.Bq 5579 = (257243932920206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5579 = 257243932920206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5579 = (13579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5580) ≤ val WuPaper.ClassicalFourthData.Bq 5580
    have hp : val WuPaper.ClassicalFourthData.Bq 5580 = (257255738103942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5580 = 257255738103942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5580 = (679:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5581) ≤ val WuPaper.ClassicalFourthData.Bq 5581
    have hp : val WuPaper.ClassicalFourthData.Bq 5581 = (257267538339990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5581 = 257267538339990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5581 = (13581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5582) ≤ val WuPaper.ClassicalFourthData.Bq 5582
    have hp : val WuPaper.ClassicalFourthData.Bq 5582 = (257279333630112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5582 = 257279333630112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5582 = (6791:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5583) ≤ val WuPaper.ClassicalFourthData.Bq 5583
    have hp : val WuPaper.ClassicalFourthData.Bq 5583 = (257291123976070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5583 = 257291123976070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5583 = (13583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5583
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_348
