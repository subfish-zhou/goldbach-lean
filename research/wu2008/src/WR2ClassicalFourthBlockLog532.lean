import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints532
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_532 (j : Fin 16) (hj : 16*532+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*532+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*532+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8512) ≤ val WuPaper.ClassicalFourthData.Bq 8512
    have hp : val WuPaper.ClassicalFourthData.Bq 8512 = (276258193481162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8512 = 276258193481162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8512 = (516:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8513) ≤ val WuPaper.ClassicalFourthData.Bq 8513
    have hp : val WuPaper.ClassicalFourthData.Bq 8513 = (276260823053404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8513 = 276260823053404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8513 = (16513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8514) ≤ val WuPaper.ClassicalFourthData.Bq 8514
    have hp : val WuPaper.ClassicalFourthData.Bq 8514 = (276263450760199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8514 = 276263450760199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8514 = (8257:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8515) ≤ val WuPaper.ClassicalFourthData.Bq 8515
    have hp : val WuPaper.ClassicalFourthData.Bq 8515 = (276266076602134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8515 = 276266076602134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8515 = (3303:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8516) ≤ val WuPaper.ClassicalFourthData.Bq 8516
    have hp : val WuPaper.ClassicalFourthData.Bq 8516 = (276268700579795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8516 = 276268700579795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8516 = (4129:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8517) ≤ val WuPaper.ClassicalFourthData.Bq 8517
    have hp : val WuPaper.ClassicalFourthData.Bq 8517 = (276271322693767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8517 = 276271322693767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8517 = (16517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8518) ≤ val WuPaper.ClassicalFourthData.Bq 8518
    have hp : val WuPaper.ClassicalFourthData.Bq 8518 = (276273942944637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8518 = 276273942944637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8518 = (8259:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8519) ≤ val WuPaper.ClassicalFourthData.Bq 8519
    have hp : val WuPaper.ClassicalFourthData.Bq 8519 = (276276561332988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8519 = 276276561332988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8519 = (16519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8519
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8520) ≤ val WuPaper.ClassicalFourthData.Bq 8520
    have hp : val WuPaper.ClassicalFourthData.Bq 8520 = (276279177859406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8520 = 276279177859406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8520 = (413:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8521) ≤ val WuPaper.ClassicalFourthData.Bq 8521
    have hp : val WuPaper.ClassicalFourthData.Bq 8521 = (276281792524477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8521 = 276281792524477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8521 = (16521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8522) ≤ val WuPaper.ClassicalFourthData.Bq 8522
    have hp : val WuPaper.ClassicalFourthData.Bq 8522 = (276284405328784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8522 = 276284405328784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8522 = (8261:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8523) ≤ val WuPaper.ClassicalFourthData.Bq 8523
    have hp : val WuPaper.ClassicalFourthData.Bq 8523 = (276287016272912:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8523 = 276287016272912 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8523 = (16523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8524) ≤ val WuPaper.ClassicalFourthData.Bq 8524
    have hp : val WuPaper.ClassicalFourthData.Bq 8524 = (276289625357446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8524 = 276289625357446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8524 = (4131:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8525) ≤ val WuPaper.ClassicalFourthData.Bq 8525
    have hp : val WuPaper.ClassicalFourthData.Bq 8525 = (276292232582970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8525 = 276292232582970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8525 = (661:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8526) ≤ val WuPaper.ClassicalFourthData.Bq 8526
    have hp : val WuPaper.ClassicalFourthData.Bq 8526 = (276294837950067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8526 = 276294837950067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8526 = (8263:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8527) ≤ val WuPaper.ClassicalFourthData.Bq 8527
    have hp : val WuPaper.ClassicalFourthData.Bq 8527 = (276297441459321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8527 = 276297441459321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8527 = (16527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8527
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_532
