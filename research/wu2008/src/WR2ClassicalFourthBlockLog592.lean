import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints592
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_592 (j : Fin 16) (hj : 16*592+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*592+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*592+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9472) ≤ val WuPaper.ClassicalFourthData.Bq 9472
    have hp : val WuPaper.ClassicalFourthData.Bq 9472 = (278003456140247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9472 = 278003456140247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9472 = (546:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9473) ≤ val WuPaper.ClassicalFourthData.Bq 9473
    have hp : val WuPaper.ClassicalFourthData.Bq 9473 = (278004537673990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9473 = 278004537673990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9473 = (17473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9474) ≤ val WuPaper.ClassicalFourthData.Bq 9474
    have hp : val WuPaper.ClassicalFourthData.Bq 9474 = (278005617822875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9474 = 278005617822875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9474 = (8737:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9475) ≤ val WuPaper.ClassicalFourthData.Bq 9475
    have hp : val WuPaper.ClassicalFourthData.Bq 9475 = (278006696587329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9475 = 278006696587329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9475 = (699:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9476) ≤ val WuPaper.ClassicalFourthData.Bq 9476
    have hp : val WuPaper.ClassicalFourthData.Bq 9476 = (278007773967774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9476 = 278007773967774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9476 = (4369:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9477) ≤ val WuPaper.ClassicalFourthData.Bq 9477
    have hp : val WuPaper.ClassicalFourthData.Bq 9477 = (278008849964637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9477 = 278008849964637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9477 = (17477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9478) ≤ val WuPaper.ClassicalFourthData.Bq 9478
    have hp : val WuPaper.ClassicalFourthData.Bq 9478 = (278009924578341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9478 = 278009924578341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9478 = (8739:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9479) ≤ val WuPaper.ClassicalFourthData.Bq 9479
    have hp : val WuPaper.ClassicalFourthData.Bq 9479 = (278010997809311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9479 = 278010997809311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9479 = (17479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9479
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9480) ≤ val WuPaper.ClassicalFourthData.Bq 9480
    have hp : val WuPaper.ClassicalFourthData.Bq 9480 = (278012069657971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9480 = 278012069657971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9480 = (437:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9481) ≤ val WuPaper.ClassicalFourthData.Bq 9481
    have hp : val WuPaper.ClassicalFourthData.Bq 9481 = (278013140124746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9481 = 278013140124746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9481 = (17481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9482) ≤ val WuPaper.ClassicalFourthData.Bq 9482
    have hp : val WuPaper.ClassicalFourthData.Bq 9482 = (278014209210058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9482 = 278014209210058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9482 = (8741:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9483) ≤ val WuPaper.ClassicalFourthData.Bq 9483
    have hp : val WuPaper.ClassicalFourthData.Bq 9483 = (278015276914332:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9483 = 278015276914332 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9483 = (17483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9484) ≤ val WuPaper.ClassicalFourthData.Bq 9484
    have hp : val WuPaper.ClassicalFourthData.Bq 9484 = (278016343237992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9484 = 278016343237992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9484 = (4371:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9485) ≤ val WuPaper.ClassicalFourthData.Bq 9485
    have hp : val WuPaper.ClassicalFourthData.Bq 9485 = (278017408181461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9485 = 278017408181461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9485 = (3497:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9486) ≤ val WuPaper.ClassicalFourthData.Bq 9486
    have hp : val WuPaper.ClassicalFourthData.Bq 9486 = (278018471745163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9486 = 278018471745163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9486 = (8743:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9487) ≤ val WuPaper.ClassicalFourthData.Bq 9487
    have hp : val WuPaper.ClassicalFourthData.Bq 9487 = (278019533929520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9487 = 278019533929520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9487 = (17487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_592
