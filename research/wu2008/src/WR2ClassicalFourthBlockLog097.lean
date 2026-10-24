import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints097
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_097 (j : Fin 16) (hj : 16*97+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*97+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*97+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1552) ≤ val WuPaper.ClassicalFourthData.Bq 1552
    have hp : val WuPaper.ClassicalFourthData.Bq 1552 = (137296424658549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1552 = 137296424658549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1552 = (597:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1553) ≤ val WuPaper.ClassicalFourthData.Bq 1553
    have hp : val WuPaper.ClassicalFourthData.Bq 1553 = (137357463054362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1553 = 137357463054362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1553 = (9553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1554) ≤ val WuPaper.ClassicalFourthData.Bq 1554
    have hp : val WuPaper.ClassicalFourthData.Bq 1554 = (137418475095130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1554 = 137418475095130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1554 = (4777:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1555) ≤ val WuPaper.ClassicalFourthData.Bq 1555
    have hp : val WuPaper.ClassicalFourthData.Bq 1555 = (137479460794015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1555 = 137479460794015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1555 = (1911:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1556) ≤ val WuPaper.ClassicalFourthData.Bq 1556
    have hp : val WuPaper.ClassicalFourthData.Bq 1556 = (137540420164172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1556 = 137540420164172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1556 = (2389:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1557) ≤ val WuPaper.ClassicalFourthData.Bq 1557
    have hp : val WuPaper.ClassicalFourthData.Bq 1557 = (137601353218748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1557 = 137601353218748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1557 = (9557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1558) ≤ val WuPaper.ClassicalFourthData.Bq 1558
    have hp : val WuPaper.ClassicalFourthData.Bq 1558 = (137662259970882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1558 = 137662259970882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1558 = (4779:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1559) ≤ val WuPaper.ClassicalFourthData.Bq 1559
    have hp : val WuPaper.ClassicalFourthData.Bq 1559 = (137723140433704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1559 = 137723140433704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1559 = (9559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1559
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1560) ≤ val WuPaper.ClassicalFourthData.Bq 1560
    have hp : val WuPaper.ClassicalFourthData.Bq 1560 = (137783994620335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1560 = 137783994620335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1560 = (239:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1561) ≤ val WuPaper.ClassicalFourthData.Bq 1561
    have hp : val WuPaper.ClassicalFourthData.Bq 1561 = (137844822543892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1561 = 137844822543892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1561 = (9561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1562) ≤ val WuPaper.ClassicalFourthData.Bq 1562
    have hp : val WuPaper.ClassicalFourthData.Bq 1562 = (137905624217479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1562 = 137905624217479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1562 = (4781:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1563) ≤ val WuPaper.ClassicalFourthData.Bq 1563
    have hp : val WuPaper.ClassicalFourthData.Bq 1563 = (137966399654195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1563 = 137966399654195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1563 = (9563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1564) ≤ val WuPaper.ClassicalFourthData.Bq 1564
    have hp : val WuPaper.ClassicalFourthData.Bq 1564 = (138027148867130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1564 = 138027148867130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1564 = (2391:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1565) ≤ val WuPaper.ClassicalFourthData.Bq 1565
    have hp : val WuPaper.ClassicalFourthData.Bq 1565 = (138087871869365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1565 = 138087871869365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1565 = (1913:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1566) ≤ val WuPaper.ClassicalFourthData.Bq 1566
    have hp : val WuPaper.ClassicalFourthData.Bq 1566 = (138148568673974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1566 = 138148568673974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1566 = (4783:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1567) ≤ val WuPaper.ClassicalFourthData.Bq 1567
    have hp : val WuPaper.ClassicalFourthData.Bq 1567 = (138209239294024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1567 = 138209239294024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1567 = (9567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_097
