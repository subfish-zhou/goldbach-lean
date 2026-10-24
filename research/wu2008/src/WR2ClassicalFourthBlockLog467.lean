import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints467
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_467 (j : Fin 16) (hj : 16*467+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*467+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*467+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7472) ≤ val WuPaper.ClassicalFourthData.Bq 7472
    have hp : val WuPaper.ClassicalFourthData.Bq 7472 = (272392689435929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7472 = 272392689435929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7472 = (967:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7473) ≤ val WuPaper.ClassicalFourthData.Bq 7473
    have hp : val WuPaper.ClassicalFourthData.Bq 7473 = (272397618483272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7473 = 272397618483272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7473 = (15473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7474) ≤ val WuPaper.ClassicalFourthData.Bq 7474
    have hp : val WuPaper.ClassicalFourthData.Bq 7474 = (272402544929712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7474 = 272402544929712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7474 = (7737:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7475) ≤ val WuPaper.ClassicalFourthData.Bq 7475
    have hp : val WuPaper.ClassicalFourthData.Bq 7475 = (272407468776097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7475 = 272407468776097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7475 = (619:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7476) ≤ val WuPaper.ClassicalFourthData.Bq 7476
    have hp : val WuPaper.ClassicalFourthData.Bq 7476 = (272412390023271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7476 = 272412390023271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7476 = (3869:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7477) ≤ val WuPaper.ClassicalFourthData.Bq 7477
    have hp : val WuPaper.ClassicalFourthData.Bq 7477 = (272417308672081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7477 = 272417308672081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7477 = (15477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7478) ≤ val WuPaper.ClassicalFourthData.Bq 7478
    have hp : val WuPaper.ClassicalFourthData.Bq 7478 = (272422224723373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7478 = 272422224723373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7478 = (7739:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7479) ≤ val WuPaper.ClassicalFourthData.Bq 7479
    have hp : val WuPaper.ClassicalFourthData.Bq 7479 = (272427138177991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7479 = 272427138177991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7479 = (15479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7479
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7480) ≤ val WuPaper.ClassicalFourthData.Bq 7480
    have hp : val WuPaper.ClassicalFourthData.Bq 7480 = (272432049036782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7480 = 272432049036782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7480 = (387:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7481) ≤ val WuPaper.ClassicalFourthData.Bq 7481
    have hp : val WuPaper.ClassicalFourthData.Bq 7481 = (272436957300588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7481 = 272436957300588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7481 = (15481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7482) ≤ val WuPaper.ClassicalFourthData.Bq 7482
    have hp : val WuPaper.ClassicalFourthData.Bq 7482 = (272441862970255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7482 = 272441862970255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7482 = (7741:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7483) ≤ val WuPaper.ClassicalFourthData.Bq 7483
    have hp : val WuPaper.ClassicalFourthData.Bq 7483 = (272446766046627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7483 = 272446766046627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7483 = (15483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7484) ≤ val WuPaper.ClassicalFourthData.Bq 7484
    have hp : val WuPaper.ClassicalFourthData.Bq 7484 = (272451666530547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7484 = 272451666530547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7484 = (3871:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7485) ≤ val WuPaper.ClassicalFourthData.Bq 7485
    have hp : val WuPaper.ClassicalFourthData.Bq 7485 = (272456564422860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7485 = 272456564422860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7485 = (3097:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7486) ≤ val WuPaper.ClassicalFourthData.Bq 7486
    have hp : val WuPaper.ClassicalFourthData.Bq 7486 = (272461459724407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7486 = 272461459724407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7486 = (7743:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7487) ≤ val WuPaper.ClassicalFourthData.Bq 7487
    have hp : val WuPaper.ClassicalFourthData.Bq 7487 = (272466352436031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7487 = 272466352436031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7487 = (15487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_467
