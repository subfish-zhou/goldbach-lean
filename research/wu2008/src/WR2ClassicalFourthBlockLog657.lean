import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints657
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_657 (j : Fin 16) (hj : 16*657+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*657+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*657+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10512) ≤ val WuPaper.ClassicalFourthData.Bq 10512
    have hp : val WuPaper.ClassicalFourthData.Bq 10512 = (278453226546868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10512 = 278453226546868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10512 = (1157:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10513) ≤ val WuPaper.ClassicalFourthData.Bq 10513
    have hp : val WuPaper.ClassicalFourthData.Bq 10513 = (278453073748102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10513 = 278453073748102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10513 = (18513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10514) ≤ val WuPaper.ClassicalFourthData.Bq 10514
    have hp : val WuPaper.ClassicalFourthData.Bq 10514 = (278452919940083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10514 = 278452919940083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10514 = (9257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10515) ≤ val WuPaper.ClassicalFourthData.Bq 10515
    have hp : val WuPaper.ClassicalFourthData.Bq 10515 = (278452765123116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10515 = 278452765123116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10515 = (3703:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10516) ≤ val WuPaper.ClassicalFourthData.Bq 10516
    have hp : val WuPaper.ClassicalFourthData.Bq 10516 = (278452609297506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10516 = 278452609297506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10516 = (4629:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10517) ≤ val WuPaper.ClassicalFourthData.Bq 10517
    have hp : val WuPaper.ClassicalFourthData.Bq 10517 = (278452452463557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10517 = 278452452463557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10517 = (18517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10518) ≤ val WuPaper.ClassicalFourthData.Bq 10518
    have hp : val WuPaper.ClassicalFourthData.Bq 10518 = (278452294621575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10518 = 278452294621575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10518 = (9259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10519) ≤ val WuPaper.ClassicalFourthData.Bq 10519
    have hp : val WuPaper.ClassicalFourthData.Bq 10519 = (278452135771864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10519 = 278452135771864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10519 = (18519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10520) ≤ val WuPaper.ClassicalFourthData.Bq 10520
    have hp : val WuPaper.ClassicalFourthData.Bq 10520 = (278451975914728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10520 = 278451975914728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10520 = (463:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10521) ≤ val WuPaper.ClassicalFourthData.Bq 10521
    have hp : val WuPaper.ClassicalFourthData.Bq 10521 = (278451815050471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10521 = 278451815050471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10521 = (18521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10522) ≤ val WuPaper.ClassicalFourthData.Bq 10522
    have hp : val WuPaper.ClassicalFourthData.Bq 10522 = (278451653179398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10522 = 278451653179398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10522 = (9261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10523) ≤ val WuPaper.ClassicalFourthData.Bq 10523
    have hp : val WuPaper.ClassicalFourthData.Bq 10523 = (278451490301813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10523 = 278451490301813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10523 = (18523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10524) ≤ val WuPaper.ClassicalFourthData.Bq 10524
    have hp : val WuPaper.ClassicalFourthData.Bq 10524 = (278451326418019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10524 = 278451326418019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10524 = (4631:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10525) ≤ val WuPaper.ClassicalFourthData.Bq 10525
    have hp : val WuPaper.ClassicalFourthData.Bq 10525 = (278451161528321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10525 = 278451161528321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10525 = (741:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10526) ≤ val WuPaper.ClassicalFourthData.Bq 10526
    have hp : val WuPaper.ClassicalFourthData.Bq 10526 = (278450995633022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10526 = 278450995633022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10526 = (9263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10527) ≤ val WuPaper.ClassicalFourthData.Bq 10527
    have hp : val WuPaper.ClassicalFourthData.Bq 10527 = (278450828732427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10527 = 278450828732427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10527 = (18527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_657
