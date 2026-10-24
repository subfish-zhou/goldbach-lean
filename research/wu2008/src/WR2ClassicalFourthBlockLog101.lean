import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints101
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_101 (j : Fin 16) (hj : 16*101+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*101+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*101+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1616) ≤ val WuPaper.ClassicalFourthData.Bq 1616
    have hp : val WuPaper.ClassicalFourthData.Bq 1616 = (141150293512321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1616 = 141150293512321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1616 = (601:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1617) ≤ val WuPaper.ClassicalFourthData.Bq 1617
    have hp : val WuPaper.ClassicalFourthData.Bq 1617 = (141209671386256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1617 = 141209671386256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1617 = (9617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1618) ≤ val WuPaper.ClassicalFourthData.Bq 1618
    have hp : val WuPaper.ClassicalFourthData.Bq 1618 = (141269023731405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1618 = 141269023731405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1618 = (4809:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1619) ≤ val WuPaper.ClassicalFourthData.Bq 1619
    have hp : val WuPaper.ClassicalFourthData.Bq 1619 = (141328350560421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1619 = 141328350560421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1619 = (9619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1620) ≤ val WuPaper.ClassicalFourthData.Bq 1620
    have hp : val WuPaper.ClassicalFourthData.Bq 1620 = (141387651885950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1620 = 141387651885950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1620 = (481:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1621) ≤ val WuPaper.ClassicalFourthData.Bq 1621
    have hp : val WuPaper.ClassicalFourthData.Bq 1621 = (141446927720631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1621 = 141446927720631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1621 = (9621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1622) ≤ val WuPaper.ClassicalFourthData.Bq 1622
    have hp : val WuPaper.ClassicalFourthData.Bq 1622 = (141506178077094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1622 = 141506178077094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1622 = (4811:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1623) ≤ val WuPaper.ClassicalFourthData.Bq 1623
    have hp : val WuPaper.ClassicalFourthData.Bq 1623 = (141565402967962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1623 = 141565402967962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1623 = (9623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1623
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1624) ≤ val WuPaper.ClassicalFourthData.Bq 1624
    have hp : val WuPaper.ClassicalFourthData.Bq 1624 = (141624602405850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1624 = 141624602405850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1624 = (1203:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1625) ≤ val WuPaper.ClassicalFourthData.Bq 1625
    have hp : val WuPaper.ClassicalFourthData.Bq 1625 = (141683776403364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1625 = 141683776403364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1625 = (77:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1626) ≤ val WuPaper.ClassicalFourthData.Bq 1626
    have hp : val WuPaper.ClassicalFourthData.Bq 1626 = (141742924973104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1626 = 141742924973104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1626 = (4813:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1627) ≤ val WuPaper.ClassicalFourthData.Bq 1627
    have hp : val WuPaper.ClassicalFourthData.Bq 1627 = (141802048127663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1627 = 141802048127663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1627 = (9627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1628) ≤ val WuPaper.ClassicalFourthData.Bq 1628
    have hp : val WuPaper.ClassicalFourthData.Bq 1628 = (141861145879623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1628 = 141861145879623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1628 = (2407:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1629) ≤ val WuPaper.ClassicalFourthData.Bq 1629
    have hp : val WuPaper.ClassicalFourthData.Bq 1629 = (141920218241562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1629 = 141920218241562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1629 = (9629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1630) ≤ val WuPaper.ClassicalFourthData.Bq 1630
    have hp : val WuPaper.ClassicalFourthData.Bq 1630 = (141979265226048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1630 = 141979265226048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1630 = (963:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1631) ≤ val WuPaper.ClassicalFourthData.Bq 1631
    have hp : val WuPaper.ClassicalFourthData.Bq 1631 = (142038286845641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1631 = 142038286845641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1631 = (9631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1631
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_101
