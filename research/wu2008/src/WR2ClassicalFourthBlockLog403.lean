import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints403
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_403 (j : Fin 16) (hj : 16*403+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*403+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*403+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6448) ≤ val WuPaper.ClassicalFourthData.Bq 6448
    have hp : val WuPaper.ClassicalFourthData.Bq 6448 = (265812904599736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6448 = 265812904599736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6448 = (903:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6449) ≤ val WuPaper.ClassicalFourthData.Bq 6449
    have hp : val WuPaper.ClassicalFourthData.Bq 6449 = (265821003234036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6449 = 265821003234036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6449 = (14449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6450) ≤ val WuPaper.ClassicalFourthData.Bq 6450
    have hp : val WuPaper.ClassicalFourthData.Bq 6450 = (265829098212039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6450 = 265829098212039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6450 = (289:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6451) ≤ val WuPaper.ClassicalFourthData.Bq 6451
    have hp : val WuPaper.ClassicalFourthData.Bq 6451 = (265837189534991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6451 = 265837189534991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6451 = (14451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6452) ≤ val WuPaper.ClassicalFourthData.Bq 6452
    have hp : val WuPaper.ClassicalFourthData.Bq 6452 = (265845277204134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6452 = 265845277204134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6452 = (3613:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6453) ≤ val WuPaper.ClassicalFourthData.Bq 6453
    have hp : val WuPaper.ClassicalFourthData.Bq 6453 = (265853361220713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6453 = 265853361220713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6453 = (14453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6454) ≤ val WuPaper.ClassicalFourthData.Bq 6454
    have hp : val WuPaper.ClassicalFourthData.Bq 6454 = (265861441585970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6454 = 265861441585970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6454 = (7227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6455) ≤ val WuPaper.ClassicalFourthData.Bq 6455
    have hp : val WuPaper.ClassicalFourthData.Bq 6455 = (265869518301147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6455 = 265869518301147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6455 = (2891:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6456) ≤ val WuPaper.ClassicalFourthData.Bq 6456
    have hp : val WuPaper.ClassicalFourthData.Bq 6456 = (265877591367486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6456 = 265877591367486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6456 = (1807:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6457) ≤ val WuPaper.ClassicalFourthData.Bq 6457
    have hp : val WuPaper.ClassicalFourthData.Bq 6457 = (265885660786228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6457 = 265885660786228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6457 = (14457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6458) ≤ val WuPaper.ClassicalFourthData.Bq 6458
    have hp : val WuPaper.ClassicalFourthData.Bq 6458 = (265893726558614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6458 = 265893726558614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6458 = (7229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6459) ≤ val WuPaper.ClassicalFourthData.Bq 6459
    have hp : val WuPaper.ClassicalFourthData.Bq 6459 = (265901788685885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6459 = 265901788685885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6459 = (14459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6460) ≤ val WuPaper.ClassicalFourthData.Bq 6460
    have hp : val WuPaper.ClassicalFourthData.Bq 6460 = (265909847169281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6460 = 265909847169281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6460 = (723:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6461) ≤ val WuPaper.ClassicalFourthData.Bq 6461
    have hp : val WuPaper.ClassicalFourthData.Bq 6461 = (265917902010040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6461 = 265917902010040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6461 = (14461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6462) ≤ val WuPaper.ClassicalFourthData.Bq 6462
    have hp : val WuPaper.ClassicalFourthData.Bq 6462 = (265925953209402:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6462 = 265925953209402 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6462 = (7231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6463) ≤ val WuPaper.ClassicalFourthData.Bq 6463
    have hp : val WuPaper.ClassicalFourthData.Bq 6463 = (265934000768605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6463 = 265934000768605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6463 = (14463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_403
