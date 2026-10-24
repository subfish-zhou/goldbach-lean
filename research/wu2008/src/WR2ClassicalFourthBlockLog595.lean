import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints595
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_595 (j : Fin 16) (hj : 16*595+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*595+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*595+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9520) ≤ val WuPaper.ClassicalFourthData.Bq 9520
    have hp : val WuPaper.ClassicalFourthData.Bq 9520 = (278053814963204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9520 = 278053814963204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9520 = (219:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9521) ≤ val WuPaper.ClassicalFourthData.Bq 9521
    have hp : val WuPaper.ClassicalFourthData.Bq 9521 = (278054830500704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9521 = 278054830500704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9521 = (17521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9522) ≤ val WuPaper.ClassicalFourthData.Bq 9522
    have hp : val WuPaper.ClassicalFourthData.Bq 9522 = (278055844673587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9522 = 278055844673587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9522 = (8761:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9523) ≤ val WuPaper.ClassicalFourthData.Bq 9523
    have hp : val WuPaper.ClassicalFourthData.Bq 9523 = (278056857482271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9523 = 278056857482271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9523 = (17523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9524) ≤ val WuPaper.ClassicalFourthData.Bq 9524
    have hp : val WuPaper.ClassicalFourthData.Bq 9524 = (278057868927174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9524 = 278057868927174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9524 = (4381:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9525) ≤ val WuPaper.ClassicalFourthData.Bq 9525
    have hp : val WuPaper.ClassicalFourthData.Bq 9525 = (278058879008714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9525 = 278058879008714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9525 = (701:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9526) ≤ val WuPaper.ClassicalFourthData.Bq 9526
    have hp : val WuPaper.ClassicalFourthData.Bq 9526 = (278059887727309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9526 = 278059887727309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9526 = (8763:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9527) ≤ val WuPaper.ClassicalFourthData.Bq 9527
    have hp : val WuPaper.ClassicalFourthData.Bq 9527 = (278060895083377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9527 = 278060895083377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9527 = (17527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9527
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9528) ≤ val WuPaper.ClassicalFourthData.Bq 9528
    have hp : val WuPaper.ClassicalFourthData.Bq 9528 = (278061901077335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9528 = 278061901077335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9528 = (2191:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9529) ≤ val WuPaper.ClassicalFourthData.Bq 9529
    have hp : val WuPaper.ClassicalFourthData.Bq 9529 = (278062905709602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9529 = 278062905709602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9529 = (17529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9530) ≤ val WuPaper.ClassicalFourthData.Bq 9530
    have hp : val WuPaper.ClassicalFourthData.Bq 9530 = (278063908980593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9530 = 278063908980593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9530 = (1753:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9531) ≤ val WuPaper.ClassicalFourthData.Bq 9531
    have hp : val WuPaper.ClassicalFourthData.Bq 9531 = (278064910890727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9531 = 278064910890727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9531 = (17531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9532) ≤ val WuPaper.ClassicalFourthData.Bq 9532
    have hp : val WuPaper.ClassicalFourthData.Bq 9532 = (278065911440421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9532 = 278065911440421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9532 = (4383:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9533) ≤ val WuPaper.ClassicalFourthData.Bq 9533
    have hp : val WuPaper.ClassicalFourthData.Bq 9533 = (278066910630091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9533 = 278066910630091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9533 = (17533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9534) ≤ val WuPaper.ClassicalFourthData.Bq 9534
    have hp : val WuPaper.ClassicalFourthData.Bq 9534 = (278067908460154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9534 = 278067908460154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9534 = (8767:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9535) ≤ val WuPaper.ClassicalFourthData.Bq 9535
    have hp : val WuPaper.ClassicalFourthData.Bq 9535 = (278068904931027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9535 = 278068904931027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9535 = (3507:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_595
