import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints656
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_656 (j : Fin 16) (hj : 16*656+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*656+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*656+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10496) ≤ val WuPaper.ClassicalFourthData.Bq 10496
    have hp : val WuPaper.ClassicalFourthData.Bq 10496 = (278455533819636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10496 = 278455533819636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10496 = (578:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10497) ≤ val WuPaper.ClassicalFourthData.Bq 10497
    have hp : val WuPaper.ClassicalFourthData.Bq 10497 = (278455397210451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10497 = 278455397210451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10497 = (18497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10498) ≤ val WuPaper.ClassicalFourthData.Bq 10498
    have hp : val WuPaper.ClassicalFourthData.Bq 10498 = (278455259587123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10498 = 278455259587123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10498 = (9249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10499) ≤ val WuPaper.ClassicalFourthData.Bq 10499
    have hp : val WuPaper.ClassicalFourthData.Bq 10499 = (278455120949957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10499 = 278455120949957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10499 = (18499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10500) ≤ val WuPaper.ClassicalFourthData.Bq 10500
    have hp : val WuPaper.ClassicalFourthData.Bq 10500 = (278454981299261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10500 = 278454981299261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10500 = (37:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10501) ≤ val WuPaper.ClassicalFourthData.Bq 10501
    have hp : val WuPaper.ClassicalFourthData.Bq 10501 = (278454840635340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10501 = 278454840635340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10501 = (18501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10502) ≤ val WuPaper.ClassicalFourthData.Bq 10502
    have hp : val WuPaper.ClassicalFourthData.Bq 10502 = (278454698958501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10502 = 278454698958501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10502 = (9251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10503) ≤ val WuPaper.ClassicalFourthData.Bq 10503
    have hp : val WuPaper.ClassicalFourthData.Bq 10503 = (278454556269049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10503 = 278454556269049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10503 = (18503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10504) ≤ val WuPaper.ClassicalFourthData.Bq 10504
    have hp : val WuPaper.ClassicalFourthData.Bq 10504 = (278454412567291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10504 = 278454412567291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10504 = (2313:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10505) ≤ val WuPaper.ClassicalFourthData.Bq 10505
    have hp : val WuPaper.ClassicalFourthData.Bq 10505 = (278454267853532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10505 = 278454267853532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10505 = (3701:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10506) ≤ val WuPaper.ClassicalFourthData.Bq 10506
    have hp : val WuPaper.ClassicalFourthData.Bq 10506 = (278454122128078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10506 = 278454122128078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10506 = (9253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10507) ≤ val WuPaper.ClassicalFourthData.Bq 10507
    have hp : val WuPaper.ClassicalFourthData.Bq 10507 = (278453975391235:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10507 = 278453975391235 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10507 = (18507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10508) ≤ val WuPaper.ClassicalFourthData.Bq 10508
    have hp : val WuPaper.ClassicalFourthData.Bq 10508 = (278453827643308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10508 = 278453827643308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10508 = (4627:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10509) ≤ val WuPaper.ClassicalFourthData.Bq 10509
    have hp : val WuPaper.ClassicalFourthData.Bq 10509 = (278453678884602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10509 = 278453678884602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10509 = (18509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10510) ≤ val WuPaper.ClassicalFourthData.Bq 10510
    have hp : val WuPaper.ClassicalFourthData.Bq 10510 = (278453529115424:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10510 = 278453529115424 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10510 = (1851:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10511) ≤ val WuPaper.ClassicalFourthData.Bq 10511
    have hp : val WuPaper.ClassicalFourthData.Bq 10511 = (278453378336077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10511 = 278453378336077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10511 = (18511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_656
