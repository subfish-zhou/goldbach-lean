import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints092
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_092 (j : Fin 16) (hj : 16*92+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*92+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*92+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1472) ≤ val WuPaper.ClassicalFourthData.Bq 1472
    have hp : val WuPaper.ClassicalFourthData.Bq 1472 = (132326781756909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1472 = 132326781756909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1472 = (296:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1473) ≤ val WuPaper.ClassicalFourthData.Bq 1473
    have hp : val WuPaper.ClassicalFourthData.Bq 1473 = (132389971937883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1473 = 132389971937883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1473 = (9473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1474) ≤ val WuPaper.ClassicalFourthData.Bq 1474
    have hp : val WuPaper.ClassicalFourthData.Bq 1474 = (132453134683807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1474 = 132453134683807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1474 = (4737:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1475) ≤ val WuPaper.ClassicalFourthData.Bq 1475
    have hp : val WuPaper.ClassicalFourthData.Bq 1475 = (132516270008517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1475 = 132516270008517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1475 = (379:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1476) ≤ val WuPaper.ClassicalFourthData.Bq 1476
    have hp : val WuPaper.ClassicalFourthData.Bq 1476 = (132579377925839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1476 = 132579377925839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1476 = (2369:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1477) ≤ val WuPaper.ClassicalFourthData.Bq 1477
    have hp : val WuPaper.ClassicalFourthData.Bq 1477 = (132642458449592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1477 = 132642458449592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1477 = (9477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1478) ≤ val WuPaper.ClassicalFourthData.Bq 1478
    have hp : val WuPaper.ClassicalFourthData.Bq 1478 = (132705511593584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1478 = 132705511593584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1478 = (4739:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1479) ≤ val WuPaper.ClassicalFourthData.Bq 1479
    have hp : val WuPaper.ClassicalFourthData.Bq 1479 = (132768537371617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1479 = 132768537371617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1479 = (9479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1479
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1480) ≤ val WuPaper.ClassicalFourthData.Bq 1480
    have hp : val WuPaper.ClassicalFourthData.Bq 1480 = (132831535797483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1480 = 132831535797483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1480 = (237:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1481) ≤ val WuPaper.ClassicalFourthData.Bq 1481
    have hp : val WuPaper.ClassicalFourthData.Bq 1481 = (132894506884966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1481 = 132894506884966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1481 = (9481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1482) ≤ val WuPaper.ClassicalFourthData.Bq 1482
    have hp : val WuPaper.ClassicalFourthData.Bq 1482 = (132957450647840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1482 = 132957450647840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1482 = (4741:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1483) ≤ val WuPaper.ClassicalFourthData.Bq 1483
    have hp : val WuPaper.ClassicalFourthData.Bq 1483 = (133020367099872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1483 = 133020367099872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1483 = (9483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1484) ≤ val WuPaper.ClassicalFourthData.Bq 1484
    have hp : val WuPaper.ClassicalFourthData.Bq 1484 = (133083256254820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1484 = 133083256254820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1484 = (2371:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1485) ≤ val WuPaper.ClassicalFourthData.Bq 1485
    have hp : val WuPaper.ClassicalFourthData.Bq 1485 = (133146118126433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1485 = 133146118126433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1485 = (1897:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1486) ≤ val WuPaper.ClassicalFourthData.Bq 1486
    have hp : val WuPaper.ClassicalFourthData.Bq 1486 = (133208952728451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1486 = 133208952728451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1486 = (4743:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1487) ≤ val WuPaper.ClassicalFourthData.Bq 1487
    have hp : val WuPaper.ClassicalFourthData.Bq 1487 = (133271760074607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1487 = 133271760074607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1487 = (9487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_092
