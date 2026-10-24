import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints090
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_090 (j : Fin 16) (hj : 16*90+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*90+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*90+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1440) ≤ val WuPaper.ClassicalFourthData.Bq 1440
    have hp : val WuPaper.ClassicalFourthData.Bq 1440 = (130290127011848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1440 = 130290127011848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1440 = (59:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1441) ≤ val WuPaper.ClassicalFourthData.Bq 1441
    have hp : val WuPaper.ClassicalFourthData.Bq 1441 = (130354202471729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1441 = 130354202471729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1441 = (9441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1442) ≤ val WuPaper.ClassicalFourthData.Bq 1442
    have hp : val WuPaper.ClassicalFourthData.Bq 1442 = (130418250049212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1442 = 130418250049212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1442 = (4721:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1443) ≤ val WuPaper.ClassicalFourthData.Bq 1443
    have hp : val WuPaper.ClassicalFourthData.Bq 1443 = (130482269758413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1443 = 130482269758413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1443 = (9443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1444) ≤ val WuPaper.ClassicalFourthData.Bq 1444
    have hp : val WuPaper.ClassicalFourthData.Bq 1444 = (130546261613439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1444 = 130546261613439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1444 = (2361:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1445) ≤ val WuPaper.ClassicalFourthData.Bq 1445
    have hp : val WuPaper.ClassicalFourthData.Bq 1445 = (130610225628389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1445 = 130610225628389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1445 = (1889:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1446) ≤ val WuPaper.ClassicalFourthData.Bq 1446
    have hp : val WuPaper.ClassicalFourthData.Bq 1446 = (130674161817353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1446 = 130674161817353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1446 = (4723:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1447) ≤ val WuPaper.ClassicalFourthData.Bq 1447
    have hp : val WuPaper.ClassicalFourthData.Bq 1447 = (130738070194410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1447 = 130738070194410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1447 = (9447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1447
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1448) ≤ val WuPaper.ClassicalFourthData.Bq 1448
    have hp : val WuPaper.ClassicalFourthData.Bq 1448 = (130801950773633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1448 = 130801950773633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1448 = (1181:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1449) ≤ val WuPaper.ClassicalFourthData.Bq 1449
    have hp : val WuPaper.ClassicalFourthData.Bq 1449 = (130865803569085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1449 = 130865803569085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1449 = (9449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1450) ≤ val WuPaper.ClassicalFourthData.Bq 1450
    have hp : val WuPaper.ClassicalFourthData.Bq 1450 = (130929628594820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1450 = 130929628594820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1450 = (189:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1451) ≤ val WuPaper.ClassicalFourthData.Bq 1451
    have hp : val WuPaper.ClassicalFourthData.Bq 1451 = (130993425864884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1451 = 130993425864884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1451 = (9451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1452) ≤ val WuPaper.ClassicalFourthData.Bq 1452
    have hp : val WuPaper.ClassicalFourthData.Bq 1452 = (131057195393312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1452 = 131057195393312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1452 = (2363:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1453) ≤ val WuPaper.ClassicalFourthData.Bq 1453
    have hp : val WuPaper.ClassicalFourthData.Bq 1453 = (131120937194133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1453 = 131120937194133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1453 = (9453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1454) ≤ val WuPaper.ClassicalFourthData.Bq 1454
    have hp : val WuPaper.ClassicalFourthData.Bq 1454 = (131184651281365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1454 = 131184651281365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1454 = (4727:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1455) ≤ val WuPaper.ClassicalFourthData.Bq 1455
    have hp : val WuPaper.ClassicalFourthData.Bq 1455 = (131248337669019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1455 = 131248337669019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1455 = (1891:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_090
