import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints103
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_103 (j : Fin 16) (hj : 16*103+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*103+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*103+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1648) ≤ val WuPaper.ClassicalFourthData.Bq 1648
    have hp : val WuPaper.ClassicalFourthData.Bq 1648 = (143037785684516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1648 = 143037785684516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1648 = (603:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1649) ≤ val WuPaper.ClassicalFourthData.Bq 1649
    have hp : val WuPaper.ClassicalFourthData.Bq 1649 = (143096352875214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1649 = 143096352875214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1649 = (9649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1650) ≤ val WuPaper.ClassicalFourthData.Bq 1650
    have hp : val WuPaper.ClassicalFourthData.Bq 1650 = (143154894938222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1650 = 143154894938222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1650 = (193:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1651) ≤ val WuPaper.ClassicalFourthData.Bq 1651
    have hp : val WuPaper.ClassicalFourthData.Bq 1651 = (143213411885946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1651 = 143213411885946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1651 = (9651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1652) ≤ val WuPaper.ClassicalFourthData.Bq 1652
    have hp : val WuPaper.ClassicalFourthData.Bq 1652 = (143271903730788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1652 = 143271903730788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1652 = (2413:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1653) ≤ val WuPaper.ClassicalFourthData.Bq 1653
    have hp : val WuPaper.ClassicalFourthData.Bq 1653 = (143330370485140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1653 = 143330370485140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1653 = (9653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1654) ≤ val WuPaper.ClassicalFourthData.Bq 1654
    have hp : val WuPaper.ClassicalFourthData.Bq 1654 = (143388812161388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1654 = 143388812161388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1654 = (4827:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1655) ≤ val WuPaper.ClassicalFourthData.Bq 1655
    have hp : val WuPaper.ClassicalFourthData.Bq 1655 = (143447228771909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1655 = 143447228771909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1655 = (1931:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1655
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1656) ≤ val WuPaper.ClassicalFourthData.Bq 1656
    have hp : val WuPaper.ClassicalFourthData.Bq 1656 = (143505620329073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1656 = 143505620329073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1656 = (1207:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1657) ≤ val WuPaper.ClassicalFourthData.Bq 1657
    have hp : val WuPaper.ClassicalFourthData.Bq 1657 = (143563986845244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1657 = 143563986845244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1657 = (9657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1658) ≤ val WuPaper.ClassicalFourthData.Bq 1658
    have hp : val WuPaper.ClassicalFourthData.Bq 1658 = (143622328332775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1658 = 143622328332775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1658 = (4829:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1659) ≤ val WuPaper.ClassicalFourthData.Bq 1659
    have hp : val WuPaper.ClassicalFourthData.Bq 1659 = (143680644804016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1659 = 143680644804016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1659 = (9659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1660) ≤ val WuPaper.ClassicalFourthData.Bq 1660
    have hp : val WuPaper.ClassicalFourthData.Bq 1660 = (143738936271305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1660 = 143738936271305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1660 = (483:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1661) ≤ val WuPaper.ClassicalFourthData.Bq 1661
    have hp : val WuPaper.ClassicalFourthData.Bq 1661 = (143797202746976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1661 = 143797202746976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1661 = (9661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1662) ≤ val WuPaper.ClassicalFourthData.Bq 1662
    have hp : val WuPaper.ClassicalFourthData.Bq 1662 = (143855444243353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1662 = 143855444243353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1662 = (4831:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1663) ≤ val WuPaper.ClassicalFourthData.Bq 1663
    have hp : val WuPaper.ClassicalFourthData.Bq 1663 = (143913660772753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1663 = 143913660772753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1663 = (9663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_103
