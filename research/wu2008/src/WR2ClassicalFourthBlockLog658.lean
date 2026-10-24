import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints658
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_658 (j : Fin 16) (hj : 16*658+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*658+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*658+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10528) ≤ val WuPaper.ClassicalFourthData.Bq 10528
    have hp : val WuPaper.ClassicalFourthData.Bq 10528 = (278450660826839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10528 = 278450660826839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10528 = (579:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10529) ≤ val WuPaper.ClassicalFourthData.Bq 10529
    have hp : val WuPaper.ClassicalFourthData.Bq 10529 = (278450491916561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10529 = 278450491916561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10529 = (18529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10530) ≤ val WuPaper.ClassicalFourthData.Bq 10530
    have hp : val WuPaper.ClassicalFourthData.Bq 10530 = (278450322001896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10530 = 278450322001896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10530 = (1853:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10531) ≤ val WuPaper.ClassicalFourthData.Bq 10531
    have hp : val WuPaper.ClassicalFourthData.Bq 10531 = (278450151083149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10531 = 278450151083149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10531 = (18531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10532) ≤ val WuPaper.ClassicalFourthData.Bq 10532
    have hp : val WuPaper.ClassicalFourthData.Bq 10532 = (278449979160623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10532 = 278449979160623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10532 = (4633:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10533) ≤ val WuPaper.ClassicalFourthData.Bq 10533
    have hp : val WuPaper.ClassicalFourthData.Bq 10533 = (278449806234619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10533 = 278449806234619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10533 = (18533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10534) ≤ val WuPaper.ClassicalFourthData.Bq 10534
    have hp : val WuPaper.ClassicalFourthData.Bq 10534 = (278449632305443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10534 = 278449632305443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10534 = (9267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10535) ≤ val WuPaper.ClassicalFourthData.Bq 10535
    have hp : val WuPaper.ClassicalFourthData.Bq 10535 = (278449457373396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10535 = 278449457373396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10535 = (3707:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10536) ≤ val WuPaper.ClassicalFourthData.Bq 10536
    have hp : val WuPaper.ClassicalFourthData.Bq 10536 = (278449281438782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10536 = 278449281438782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10536 = (2317:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10537) ≤ val WuPaper.ClassicalFourthData.Bq 10537
    have hp : val WuPaper.ClassicalFourthData.Bq 10537 = (278449104501903:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10537 = 278449104501903 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10537 = (18537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10538) ≤ val WuPaper.ClassicalFourthData.Bq 10538
    have hp : val WuPaper.ClassicalFourthData.Bq 10538 = (278448926563062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10538 = 278448926563062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10538 = (9269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10539) ≤ val WuPaper.ClassicalFourthData.Bq 10539
    have hp : val WuPaper.ClassicalFourthData.Bq 10539 = (278448747622561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10539 = 278448747622561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10539 = (18539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10540) ≤ val WuPaper.ClassicalFourthData.Bq 10540
    have hp : val WuPaper.ClassicalFourthData.Bq 10540 = (278448567680703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10540 = 278448567680703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10540 = (927:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10540
  · norm_num at hj
  · norm_num at hj
  · norm_num at hj
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_658
