import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints293
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_293 (j : Fin 16) (hj : 16*293+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*293+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*293+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4688) ≤ val WuPaper.ClassicalFourthData.Bq 4688
    have hp : val WuPaper.ClassicalFourthData.Bq 4688 = (244529761056649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4688 = 244529761056649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4688 = (793:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4689) ≤ val WuPaper.ClassicalFourthData.Bq 4689
    have hp : val WuPaper.ClassicalFourthData.Bq 4689 = (244546771766784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4689 = 244546771766784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4689 = (12689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4690) ≤ val WuPaper.ClassicalFourthData.Bq 4690
    have hp : val WuPaper.ClassicalFourthData.Bq 4690 = (244563775620934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4690 = 244563775620934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4690 = (1269:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4691) ≤ val WuPaper.ClassicalFourthData.Bq 4691
    have hp : val WuPaper.ClassicalFourthData.Bq 4691 = (244580772621680:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4691 = 244580772621680 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4691 = (12691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4692) ≤ val WuPaper.ClassicalFourthData.Bq 4692
    have hp : val WuPaper.ClassicalFourthData.Bq 4692 = (244597762771602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4692 = 244597762771602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4692 = (3173:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4693) ≤ val WuPaper.ClassicalFourthData.Bq 4693
    have hp : val WuPaper.ClassicalFourthData.Bq 4693 = (244614746073281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4693 = 244614746073281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4693 = (12693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4694) ≤ val WuPaper.ClassicalFourthData.Bq 4694
    have hp : val WuPaper.ClassicalFourthData.Bq 4694 = (244631722529293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4694 = 244631722529293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4694 = (6347:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4695) ≤ val WuPaper.ClassicalFourthData.Bq 4695
    have hp : val WuPaper.ClassicalFourthData.Bq 4695 = (244648692142216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4695 = 244648692142216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4695 = (2539:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4695
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4696) ≤ val WuPaper.ClassicalFourthData.Bq 4696
    have hp : val WuPaper.ClassicalFourthData.Bq 4696 = (244665654914625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4696 = 244665654914625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4696 = (1587:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4697) ≤ val WuPaper.ClassicalFourthData.Bq 4697
    have hp : val WuPaper.ClassicalFourthData.Bq 4697 = (244682610849095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4697 = 244682610849095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4697 = (12697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4698) ≤ val WuPaper.ClassicalFourthData.Bq 4698
    have hp : val WuPaper.ClassicalFourthData.Bq 4698 = (244699559948199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4698 = 244699559948199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4698 = (6349:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4699) ≤ val WuPaper.ClassicalFourthData.Bq 4699
    have hp : val WuPaper.ClassicalFourthData.Bq 4699 = (244716502214510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4699 = 244716502214510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4699 = (12699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4700) ≤ val WuPaper.ClassicalFourthData.Bq 4700
    have hp : val WuPaper.ClassicalFourthData.Bq 4700 = (244733437650598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4700 = 244733437650598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4700 = (127:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4701) ≤ val WuPaper.ClassicalFourthData.Bq 4701
    have hp : val WuPaper.ClassicalFourthData.Bq 4701 = (244750366259034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4701 = 244750366259034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4701 = (12701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4702) ≤ val WuPaper.ClassicalFourthData.Bq 4702
    have hp : val WuPaper.ClassicalFourthData.Bq 4702 = (244767288042387:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4702 = 244767288042387 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4702 = (6351:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4703) ≤ val WuPaper.ClassicalFourthData.Bq 4703
    have hp : val WuPaper.ClassicalFourthData.Bq 4703 = (244784203003224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4703 = 244784203003224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4703 = (12703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_293
