import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints100
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_100 (j : Fin 16) (hj : 16*100+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*100+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*100+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1600) ≤ val WuPaper.ClassicalFourthData.Bq 1600
    have hp : val WuPaper.ClassicalFourthData.Bq 1600 = (140196765258839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1600 = 140196765258839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1600 = (12:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1601) ≤ val WuPaper.ClassicalFourthData.Bq 1601
    have hp : val WuPaper.ClassicalFourthData.Bq 1601 = (140256553320615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1601 = 140256553320615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1601 = (9601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1602) ≤ val WuPaper.ClassicalFourthData.Bq 1602
    have hp : val WuPaper.ClassicalFourthData.Bq 1602 = (140316315650084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1602 = 140316315650084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1602 = (4801:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1603) ≤ val WuPaper.ClassicalFourthData.Bq 1603
    have hp : val WuPaper.ClassicalFourthData.Bq 1603 = (140376052260026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1603 = 140376052260026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1603 = (9603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1604) ≤ val WuPaper.ClassicalFourthData.Bq 1604
    have hp : val WuPaper.ClassicalFourthData.Bq 1604 = (140435763163212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1604 = 140435763163212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1604 = (2401:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1605) ≤ val WuPaper.ClassicalFourthData.Bq 1605
    have hp : val WuPaper.ClassicalFourthData.Bq 1605 = (140495448372403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1605 = 140495448372403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1605 = (1921:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1606) ≤ val WuPaper.ClassicalFourthData.Bq 1606
    have hp : val WuPaper.ClassicalFourthData.Bq 1606 = (140555107900357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1606 = 140555107900357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1606 = (4803:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1607) ≤ val WuPaper.ClassicalFourthData.Bq 1607
    have hp : val WuPaper.ClassicalFourthData.Bq 1607 = (140614741759819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1607 = 140614741759819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1607 = (9607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1607
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1608) ≤ val WuPaper.ClassicalFourthData.Bq 1608
    have hp : val WuPaper.ClassicalFourthData.Bq 1608 = (140674349963530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1608 = 140674349963530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1608 = (1201:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1609) ≤ val WuPaper.ClassicalFourthData.Bq 1609
    have hp : val WuPaper.ClassicalFourthData.Bq 1609 = (140733932524221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1609 = 140733932524221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1609 = (9609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1610) ≤ val WuPaper.ClassicalFourthData.Bq 1610
    have hp : val WuPaper.ClassicalFourthData.Bq 1610 = (140793489454616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1610 = 140793489454616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1610 = (961:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1611) ≤ val WuPaper.ClassicalFourthData.Bq 1611
    have hp : val WuPaper.ClassicalFourthData.Bq 1611 = (140853020767431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1611 = 140853020767431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1611 = (9611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1612) ≤ val WuPaper.ClassicalFourthData.Bq 1612
    have hp : val WuPaper.ClassicalFourthData.Bq 1612 = (140912526475375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1612 = 140912526475375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1612 = (2403:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1613) ≤ val WuPaper.ClassicalFourthData.Bq 1613
    have hp : val WuPaper.ClassicalFourthData.Bq 1613 = (140972006591147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1613 = 140972006591147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1613 = (9613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1614) ≤ val WuPaper.ClassicalFourthData.Bq 1614
    have hp : val WuPaper.ClassicalFourthData.Bq 1614 = (141031461127440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1614 = 141031461127440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1614 = (4807:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1615) ≤ val WuPaper.ClassicalFourthData.Bq 1615
    have hp : val WuPaper.ClassicalFourthData.Bq 1615 = (141090890096939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1615 = 141090890096939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1615 = (1923:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_100
