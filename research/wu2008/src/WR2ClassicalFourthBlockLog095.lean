import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints095
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_095 (j : Fin 16) (hj : 16*95+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*95+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*95+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1520) ≤ val WuPaper.ClassicalFourthData.Bq 1520
    have hp : val WuPaper.ClassicalFourthData.Bq 1520 = (135329201331561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1520 = 135329201331561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1520 = (119:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1521) ≤ val WuPaper.ClassicalFourthData.Bq 1521
    have hp : val WuPaper.ClassicalFourthData.Bq 1521 = (135391090088024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1521 = 135391090088024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1521 = (9521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1522) ≤ val WuPaper.ClassicalFourthData.Bq 1522
    have hp : val WuPaper.ClassicalFourthData.Bq 1522 = (135452952063883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1522 = 135452952063883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1522 = (4761:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1523) ≤ val WuPaper.ClassicalFourthData.Bq 1523
    have hp : val WuPaper.ClassicalFourthData.Bq 1523 = (135514787272566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1523 = 135514787272566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1523 = (9523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1524) ≤ val WuPaper.ClassicalFourthData.Bq 1524
    have hp : val WuPaper.ClassicalFourthData.Bq 1524 = (135576595727491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1524 = 135576595727491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1524 = (2381:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1525) ≤ val WuPaper.ClassicalFourthData.Bq 1525
    have hp : val WuPaper.ClassicalFourthData.Bq 1525 = (135638377442069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1525 = 135638377442069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1525 = (381:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1526) ≤ val WuPaper.ClassicalFourthData.Bq 1526
    have hp : val WuPaper.ClassicalFourthData.Bq 1526 = (135700132429702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1526 = 135700132429702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1526 = (4763:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1527) ≤ val WuPaper.ClassicalFourthData.Bq 1527
    have hp : val WuPaper.ClassicalFourthData.Bq 1527 = (135761860703784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1527 = 135761860703784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1527 = (9527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1527
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1528) ≤ val WuPaper.ClassicalFourthData.Bq 1528
    have hp : val WuPaper.ClassicalFourthData.Bq 1528 = (135823562277699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1528 = 135823562277699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1528 = (1191:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1529) ≤ val WuPaper.ClassicalFourthData.Bq 1529
    have hp : val WuPaper.ClassicalFourthData.Bq 1529 = (135885237164826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1529 = 135885237164826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1529 = (9529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1530) ≤ val WuPaper.ClassicalFourthData.Bq 1530
    have hp : val WuPaper.ClassicalFourthData.Bq 1530 = (135946885378533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1530 = 135946885378533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1530 = (953:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1531) ≤ val WuPaper.ClassicalFourthData.Bq 1531
    have hp : val WuPaper.ClassicalFourthData.Bq 1531 = (136008506932180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1531 = 136008506932180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1531 = (9531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1532) ≤ val WuPaper.ClassicalFourthData.Bq 1532
    have hp : val WuPaper.ClassicalFourthData.Bq 1532 = (136070101839120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1532 = 136070101839120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1532 = (2383:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1533) ≤ val WuPaper.ClassicalFourthData.Bq 1533
    have hp : val WuPaper.ClassicalFourthData.Bq 1533 = (136131670112696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1533 = 136131670112696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1533 = (9533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1534) ≤ val WuPaper.ClassicalFourthData.Bq 1534
    have hp : val WuPaper.ClassicalFourthData.Bq 1534 = (136193211766245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1534 = 136193211766245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1534 = (4767:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1535) ≤ val WuPaper.ClassicalFourthData.Bq 1535
    have hp : val WuPaper.ClassicalFourthData.Bq 1535 = (136254726813093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1535 = 136254726813093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1535 = (1907:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_095
