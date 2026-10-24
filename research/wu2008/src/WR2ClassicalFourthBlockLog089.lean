import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints089
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_089 (j : Fin 16) (hj : 16*89+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*89+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*89+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1424) ≤ val WuPaper.ClassicalFourthData.Bq 1424
    have hp : val WuPaper.ClassicalFourthData.Bq 1424 = (129261116094315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1424 = 129261116094315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1424 = (589:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1425) ≤ val WuPaper.ClassicalFourthData.Bq 1425
    have hp : val WuPaper.ClassicalFourthData.Bq 1425 = (129325639599632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1425 = 129325639599632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1425 = (377:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1426) ≤ val WuPaper.ClassicalFourthData.Bq 1426
    have hp : val WuPaper.ClassicalFourthData.Bq 1426 = (129390134995481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1426 = 129390134995481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1426 = (4713:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1427) ≤ val WuPaper.ClassicalFourthData.Bq 1427
    have hp : val WuPaper.ClassicalFourthData.Bq 1427 = (129454602296119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1427 = 129454602296119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1427 = (9427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1428) ≤ val WuPaper.ClassicalFourthData.Bq 1428
    have hp : val WuPaper.ClassicalFourthData.Bq 1428 = (129519041515797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1428 = 129519041515797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1428 = (2357:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1429) ≤ val WuPaper.ClassicalFourthData.Bq 1429
    have hp : val WuPaper.ClassicalFourthData.Bq 1429 = (129583452668756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1429 = 129583452668756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1429 = (9429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1430) ≤ val WuPaper.ClassicalFourthData.Bq 1430
    have hp : val WuPaper.ClassicalFourthData.Bq 1430 = (129647835769228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1430 = 129647835769228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1430 = (943:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1431) ≤ val WuPaper.ClassicalFourthData.Bq 1431
    have hp : val WuPaper.ClassicalFourthData.Bq 1431 = (129712190831436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1431 = 129712190831436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1431 = (9431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1431
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1432) ≤ val WuPaper.ClassicalFourthData.Bq 1432
    have hp : val WuPaper.ClassicalFourthData.Bq 1432 = (129776517869595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1432 = 129776517869595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1432 = (1179:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1433) ≤ val WuPaper.ClassicalFourthData.Bq 1433
    have hp : val WuPaper.ClassicalFourthData.Bq 1433 = (129840816897910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1433 = 129840816897910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1433 = (9433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1434) ≤ val WuPaper.ClassicalFourthData.Bq 1434
    have hp : val WuPaper.ClassicalFourthData.Bq 1434 = (129905087930577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1434 = 129905087930577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1434 = (4717:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1435) ≤ val WuPaper.ClassicalFourthData.Bq 1435
    have hp : val WuPaper.ClassicalFourthData.Bq 1435 = (129969330981784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1435 = 129969330981784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1435 = (1887:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1436) ≤ val WuPaper.ClassicalFourthData.Bq 1436
    have hp : val WuPaper.ClassicalFourthData.Bq 1436 = (130033546065709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1436 = 130033546065709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1436 = (2359:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1437) ≤ val WuPaper.ClassicalFourthData.Bq 1437
    have hp : val WuPaper.ClassicalFourthData.Bq 1437 = (130097733196522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1437 = 130097733196522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1437 = (9437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1438) ≤ val WuPaper.ClassicalFourthData.Bq 1438
    have hp : val WuPaper.ClassicalFourthData.Bq 1438 = (130161892388383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1438 = 130161892388383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1438 = (4719:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1439) ≤ val WuPaper.ClassicalFourthData.Bq 1439
    have hp : val WuPaper.ClassicalFourthData.Bq 1439 = (130226023655444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1439 = 130226023655444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1439 = (9439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_089
