import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints352
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_352 (j : Fin 16) (hj : 16*352+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*352+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*352+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5632) ≤ val WuPaper.ClassicalFourthData.Bq 5632
    have hp : val WuPaper.ClassicalFourthData.Bq 5632 = (257862830823527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5632 = 257862830823527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5632 = (426:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5633) ≤ val WuPaper.ClassicalFourthData.Bq 5633
    have hp : val WuPaper.ClassicalFourthData.Bq 5633 = (257874376191771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5633 = 257874376191771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5633 = (13633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5634) ≤ val WuPaper.ClassicalFourthData.Bq 5634
    have hp : val WuPaper.ClassicalFourthData.Bq 5634 = (257885916704751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5634 = 257885916704751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5634 = (6817:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5635) ≤ val WuPaper.ClassicalFourthData.Bq 5635
    have hp : val WuPaper.ClassicalFourthData.Bq 5635 = (257897452364194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5635 = 257897452364194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5635 = (2727:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5636) ≤ val WuPaper.ClassicalFourthData.Bq 5636
    have hp : val WuPaper.ClassicalFourthData.Bq 5636 = (257908983171822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5636 = 257908983171822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5636 = (3409:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5637) ≤ val WuPaper.ClassicalFourthData.Bq 5637
    have hp : val WuPaper.ClassicalFourthData.Bq 5637 = (257920509129359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5637 = 257920509129359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5637 = (13637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5638) ≤ val WuPaper.ClassicalFourthData.Bq 5638
    have hp : val WuPaper.ClassicalFourthData.Bq 5638 = (257932030238527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5638 = 257932030238527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5638 = (6819:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5639) ≤ val WuPaper.ClassicalFourthData.Bq 5639
    have hp : val WuPaper.ClassicalFourthData.Bq 5639 = (257943546501048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5639 = 257943546501048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5639 = (13639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5639
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5640) ≤ val WuPaper.ClassicalFourthData.Bq 5640
    have hp : val WuPaper.ClassicalFourthData.Bq 5640 = (257955057918642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5640 = 257955057918642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5640 = (341:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5641) ≤ val WuPaper.ClassicalFourthData.Bq 5641
    have hp : val WuPaper.ClassicalFourthData.Bq 5641 = (257966564493031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5641 = 257966564493031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5641 = (13641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5642) ≤ val WuPaper.ClassicalFourthData.Bq 5642
    have hp : val WuPaper.ClassicalFourthData.Bq 5642 = (257978066225934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5642 = 257978066225934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5642 = (6821:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5643) ≤ val WuPaper.ClassicalFourthData.Bq 5643
    have hp : val WuPaper.ClassicalFourthData.Bq 5643 = (257989563119069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5643 = 257989563119069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5643 = (13643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5644) ≤ val WuPaper.ClassicalFourthData.Bq 5644
    have hp : val WuPaper.ClassicalFourthData.Bq 5644 = (258001055174154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5644 = 258001055174154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5644 = (3411:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5645) ≤ val WuPaper.ClassicalFourthData.Bq 5645
    have hp : val WuPaper.ClassicalFourthData.Bq 5645 = (258012542392908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5645 = 258012542392908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5645 = (2729:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5646) ≤ val WuPaper.ClassicalFourthData.Bq 5646
    have hp : val WuPaper.ClassicalFourthData.Bq 5646 = (258024024777047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5646 = 258024024777047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5646 = (6823:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5647) ≤ val WuPaper.ClassicalFourthData.Bq 5647
    have hp : val WuPaper.ClassicalFourthData.Bq 5647 = (258035502328287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5647 = 258035502328287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5647 = (13647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_352
