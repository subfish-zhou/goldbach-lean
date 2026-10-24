import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints651
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_651 (j : Fin 16) (hj : 16*651+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*651+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*651+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10416) ≤ val WuPaper.ClassicalFourthData.Bq 10416
    have hp : val WuPaper.ClassicalFourthData.Bq 10416 = (278463149418997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10416 = 278463149418997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10416 = (1151:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10417) ≤ val WuPaper.ClassicalFourthData.Bq 10417
    have hp : val WuPaper.ClassicalFourthData.Bq 10417 = (278463094942523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10417 = 278463094942523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10417 = (18417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10418) ≤ val WuPaper.ClassicalFourthData.Bq 10418
    have hp : val WuPaper.ClassicalFourthData.Bq 10418 = (278463039427081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10418 = 278463039427081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10418 = (9209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10419) ≤ val WuPaper.ClassicalFourthData.Bq 10419
    have hp : val WuPaper.ClassicalFourthData.Bq 10419 = (278462982872987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10419 = 278462982872987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10419 = (18419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10420) ≤ val WuPaper.ClassicalFourthData.Bq 10420
    have hp : val WuPaper.ClassicalFourthData.Bq 10420 = (278462925280552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10420 = 278462925280552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10420 = (921:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10421) ≤ val WuPaper.ClassicalFourthData.Bq 10421
    have hp : val WuPaper.ClassicalFourthData.Bq 10421 = (278462866650093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10421 = 278462866650093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10421 = (18421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10422) ≤ val WuPaper.ClassicalFourthData.Bq 10422
    have hp : val WuPaper.ClassicalFourthData.Bq 10422 = (278462806981921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10422 = 278462806981921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10422 = (9211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10423) ≤ val WuPaper.ClassicalFourthData.Bq 10423
    have hp : val WuPaper.ClassicalFourthData.Bq 10423 = (278462746276353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10423 = 278462746276353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10423 = (18423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10424) ≤ val WuPaper.ClassicalFourthData.Bq 10424
    have hp : val WuPaper.ClassicalFourthData.Bq 10424 = (278462684533700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10424 = 278462684533700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10424 = (2303:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10425) ≤ val WuPaper.ClassicalFourthData.Bq 10425
    have hp : val WuPaper.ClassicalFourthData.Bq 10425 = (278462621754276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10425 = 278462621754276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10425 = (737:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10426) ≤ val WuPaper.ClassicalFourthData.Bq 10426
    have hp : val WuPaper.ClassicalFourthData.Bq 10426 = (278462557938396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10426 = 278462557938396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10426 = (9213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10427) ≤ val WuPaper.ClassicalFourthData.Bq 10427
    have hp : val WuPaper.ClassicalFourthData.Bq 10427 = (278462493086372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10427 = 278462493086372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10427 = (18427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10428) ≤ val WuPaper.ClassicalFourthData.Bq 10428
    have hp : val WuPaper.ClassicalFourthData.Bq 10428 = (278462427198517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10428 = 278462427198517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10428 = (4607:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10429) ≤ val WuPaper.ClassicalFourthData.Bq 10429
    have hp : val WuPaper.ClassicalFourthData.Bq 10429 = (278462360275145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10429 = 278462360275145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10429 = (18429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10430) ≤ val WuPaper.ClassicalFourthData.Bq 10430
    have hp : val WuPaper.ClassicalFourthData.Bq 10430 = (278462292316569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10430 = 278462292316569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10430 = (1843:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10431) ≤ val WuPaper.ClassicalFourthData.Bq 10431
    have hp : val WuPaper.ClassicalFourthData.Bq 10431 = (278462223323102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10431 = 278462223323102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10431 = (18431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_651
