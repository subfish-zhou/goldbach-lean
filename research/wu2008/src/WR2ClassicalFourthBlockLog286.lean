import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints286
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_286 (j : Fin 16) (hj : 16*286+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*286+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*286+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4576) ≤ val WuPaper.ClassicalFourthData.Bq 4576
    have hp : val WuPaper.ClassicalFourthData.Bq 4576 = (242580548094325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4576 = 242580548094325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4576 = (393:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4577) ≤ val WuPaper.ClassicalFourthData.Bq 4577
    have hp : val WuPaper.ClassicalFourthData.Bq 4577 = (242598343289622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4577 = 242598343289622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4577 = (12577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4578) ≤ val WuPaper.ClassicalFourthData.Bq 4578
    have hp : val WuPaper.ClassicalFourthData.Bq 4578 = (242616131332422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4578 = 242616131332422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4578 = (6289:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4579) ≤ val WuPaper.ClassicalFourthData.Bq 4579
    have hp : val WuPaper.ClassicalFourthData.Bq 4579 = (242633912225436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4579 = 242633912225436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4579 = (12579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4580) ≤ val WuPaper.ClassicalFourthData.Bq 4580
    have hp : val WuPaper.ClassicalFourthData.Bq 4580 = (242651685971377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4580 = 242651685971377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4580 = (629:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4581) ≤ val WuPaper.ClassicalFourthData.Bq 4581
    have hp : val WuPaper.ClassicalFourthData.Bq 4581 = (242669452572958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4581 = 242669452572958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4581 = (12581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4582) ≤ val WuPaper.ClassicalFourthData.Bq 4582
    have hp : val WuPaper.ClassicalFourthData.Bq 4582 = (242687212032886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4582 = 242687212032886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4582 = (6291:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4583) ≤ val WuPaper.ClassicalFourthData.Bq 4583
    have hp : val WuPaper.ClassicalFourthData.Bq 4583 = (242704964353872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4583 = 242704964353872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4583 = (12583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4583
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4584) ≤ val WuPaper.ClassicalFourthData.Bq 4584
    have hp : val WuPaper.ClassicalFourthData.Bq 4584 = (242722709538623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4584 = 242722709538623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4584 = (1573:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4585) ≤ val WuPaper.ClassicalFourthData.Bq 4585
    have hp : val WuPaper.ClassicalFourthData.Bq 4585 = (242740447589845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4585 = 242740447589845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4585 = (2517:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4586) ≤ val WuPaper.ClassicalFourthData.Bq 4586
    have hp : val WuPaper.ClassicalFourthData.Bq 4586 = (242758178510243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4586 = 242758178510243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4586 = (6293:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4587) ≤ val WuPaper.ClassicalFourthData.Bq 4587
    have hp : val WuPaper.ClassicalFourthData.Bq 4587 = (242775902302521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4587 = 242775902302521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4587 = (12587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4588) ≤ val WuPaper.ClassicalFourthData.Bq 4588
    have hp : val WuPaper.ClassicalFourthData.Bq 4588 = (242793618969382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4588 = 242793618969382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4588 = (3147:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4589) ≤ val WuPaper.ClassicalFourthData.Bq 4589
    have hp : val WuPaper.ClassicalFourthData.Bq 4589 = (242811328513527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4589 = 242811328513527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4589 = (12589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4590) ≤ val WuPaper.ClassicalFourthData.Bq 4590
    have hp : val WuPaper.ClassicalFourthData.Bq 4590 = (242829030937657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4590 = 242829030937657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4590 = (1259:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4591) ≤ val WuPaper.ClassicalFourthData.Bq 4591
    have hp : val WuPaper.ClassicalFourthData.Bq 4591 = (242846726244470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4591 = 242846726244470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4591 = (12591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_286
