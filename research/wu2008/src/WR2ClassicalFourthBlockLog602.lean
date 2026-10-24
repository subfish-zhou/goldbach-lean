import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints602
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_602 (j : Fin 16) (hj : 16*602+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*602+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*602+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9632) ≤ val WuPaper.ClassicalFourthData.Bq 9632
    have hp : val WuPaper.ClassicalFourthData.Bq 9632 = (278159167200525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9632 = 278159167200525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9632 = (551:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9633) ≤ val WuPaper.ClassicalFourthData.Bq 9633
    have hp : val WuPaper.ClassicalFourthData.Bq 9633 = (278160032470262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9633 = 278160032470262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9633 = (17633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9634) ≤ val WuPaper.ClassicalFourthData.Bq 9634
    have hp : val WuPaper.ClassicalFourthData.Bq 9634 = (278160896421395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9634 = 278160896421395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9634 = (8817:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9635) ≤ val WuPaper.ClassicalFourthData.Bq 9635
    have hp : val WuPaper.ClassicalFourthData.Bq 9635 = (278161759054327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9635 = 278161759054327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9635 = (3527:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9636) ≤ val WuPaper.ClassicalFourthData.Bq 9636
    have hp : val WuPaper.ClassicalFourthData.Bq 9636 = (278162620369462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9636 = 278162620369462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9636 = (4409:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9637) ≤ val WuPaper.ClassicalFourthData.Bq 9637
    have hp : val WuPaper.ClassicalFourthData.Bq 9637 = (278163480367202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9637 = 278163480367202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9637 = (17637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9638) ≤ val WuPaper.ClassicalFourthData.Bq 9638
    have hp : val WuPaper.ClassicalFourthData.Bq 9638 = (278164339047950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9638 = 278164339047950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9638 = (8819:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9639) ≤ val WuPaper.ClassicalFourthData.Bq 9639
    have hp : val WuPaper.ClassicalFourthData.Bq 9639 = (278165196412110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9639 = 278165196412110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9639 = (17639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9639
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9640) ≤ val WuPaper.ClassicalFourthData.Bq 9640
    have hp : val WuPaper.ClassicalFourthData.Bq 9640 = (278166052460083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9640 = 278166052460083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9640 = (441:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9641) ≤ val WuPaper.ClassicalFourthData.Bq 9641
    have hp : val WuPaper.ClassicalFourthData.Bq 9641 = (278166907192273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9641 = 278166907192273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9641 = (17641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9642) ≤ val WuPaper.ClassicalFourthData.Bq 9642
    have hp : val WuPaper.ClassicalFourthData.Bq 9642 = (278167760609082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9642 = 278167760609082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9642 = (8821:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9643) ≤ val WuPaper.ClassicalFourthData.Bq 9643
    have hp : val WuPaper.ClassicalFourthData.Bq 9643 = (278168612710911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9643 = 278168612710911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9643 = (17643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9644) ≤ val WuPaper.ClassicalFourthData.Bq 9644
    have hp : val WuPaper.ClassicalFourthData.Bq 9644 = (278169463498164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9644 = 278169463498164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9644 = (4411:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9645) ≤ val WuPaper.ClassicalFourthData.Bq 9645
    have hp : val WuPaper.ClassicalFourthData.Bq 9645 = (278170312971243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9645 = 278170312971243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9645 = (3529:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9646) ≤ val WuPaper.ClassicalFourthData.Bq 9646
    have hp : val WuPaper.ClassicalFourthData.Bq 9646 = (278171161130548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9646 = 278171161130548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9646 = (8823:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9647) ≤ val WuPaper.ClassicalFourthData.Bq 9647
    have hp : val WuPaper.ClassicalFourthData.Bq 9647 = (278172007976482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9647 = 278172007976482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9647 = (17647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_602
