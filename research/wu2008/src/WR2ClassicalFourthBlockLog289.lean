import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints289
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_289 (j : Fin 16) (hj : 16*289+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*289+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*289+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4624) ≤ val WuPaper.ClassicalFourthData.Bq 4624
    have hp : val WuPaper.ClassicalFourthData.Bq 4624 = (243426696149161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4624 = 243426696149161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4624 = (789:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4625) ≤ val WuPaper.ClassicalFourthData.Bq 4625
    have hp : val WuPaper.ClassicalFourthData.Bq 4625 = (243444151064565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4625 = 243444151064565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4625 = (101:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4626) ≤ val WuPaper.ClassicalFourthData.Bq 4626
    have hp : val WuPaper.ClassicalFourthData.Bq 4626 = (243461598956364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4626 = 243461598956364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4626 = (6313:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4627) ≤ val WuPaper.ClassicalFourthData.Bq 4627
    have hp : val WuPaper.ClassicalFourthData.Bq 4627 = (243479039827212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4627 = 243479039827212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4627 = (12627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4628) ≤ val WuPaper.ClassicalFourthData.Bq 4628
    have hp : val WuPaper.ClassicalFourthData.Bq 4628 = (243496473679766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4628 = 243496473679766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4628 = (3157:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4629) ≤ val WuPaper.ClassicalFourthData.Bq 4629
    have hp : val WuPaper.ClassicalFourthData.Bq 4629 = (243513900516678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4629 = 243513900516678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4629 = (12629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4630) ≤ val WuPaper.ClassicalFourthData.Bq 4630
    have hp : val WuPaper.ClassicalFourthData.Bq 4630 = (243531320340601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4630 = 243531320340601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4630 = (1263:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4631) ≤ val WuPaper.ClassicalFourthData.Bq 4631
    have hp : val WuPaper.ClassicalFourthData.Bq 4631 = (243548733154186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4631 = 243548733154186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4631 = (12631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4631
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4632) ≤ val WuPaper.ClassicalFourthData.Bq 4632
    have hp : val WuPaper.ClassicalFourthData.Bq 4632 = (243566138960084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4632 = 243566138960084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4632 = (1579:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4633) ≤ val WuPaper.ClassicalFourthData.Bq 4633
    have hp : val WuPaper.ClassicalFourthData.Bq 4633 = (243583537760943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4633 = 243583537760943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4633 = (12633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4634) ≤ val WuPaper.ClassicalFourthData.Bq 4634
    have hp : val WuPaper.ClassicalFourthData.Bq 4634 = (243600929559410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4634 = 243600929559410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4634 = (6317:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4635) ≤ val WuPaper.ClassicalFourthData.Bq 4635
    have hp : val WuPaper.ClassicalFourthData.Bq 4635 = (243618314358133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4635 = 243618314358133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4635 = (2527:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4636) ≤ val WuPaper.ClassicalFourthData.Bq 4636
    have hp : val WuPaper.ClassicalFourthData.Bq 4636 = (243635692159757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4636 = 243635692159757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4636 = (3159:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4637) ≤ val WuPaper.ClassicalFourthData.Bq 4637
    have hp : val WuPaper.ClassicalFourthData.Bq 4637 = (243653062966926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4637 = 243653062966926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4637 = (12637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4638) ≤ val WuPaper.ClassicalFourthData.Bq 4638
    have hp : val WuPaper.ClassicalFourthData.Bq 4638 = (243670426782282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4638 = 243670426782282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4638 = (6319:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4639) ≤ val WuPaper.ClassicalFourthData.Bq 4639
    have hp : val WuPaper.ClassicalFourthData.Bq 4639 = (243687783608468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4639 = 243687783608468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4639 = (12639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_289
