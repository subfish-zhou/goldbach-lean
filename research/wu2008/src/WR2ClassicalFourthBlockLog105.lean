import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints105
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_105 (j : Fin 16) (hj : 16*105+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*105+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*105+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1680) ≤ val WuPaper.ClassicalFourthData.Bq 1680
    have hp : val WuPaper.ClassicalFourthData.Bq 1680 = (144899533724451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1680 = 144899533724451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1680 = (121:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1681) ≤ val WuPaper.ClassicalFourthData.Bq 1681
    have hp : val WuPaper.ClassicalFourthData.Bq 1681 = (144957302946018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1681 = 144957302946018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1681 = (9681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1682) ≤ val WuPaper.ClassicalFourthData.Bq 1682
    have hp : val WuPaper.ClassicalFourthData.Bq 1682 = (145015047433219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1682 = 145015047433219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1682 = (4841:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1683) ≤ val WuPaper.ClassicalFourthData.Bq 1683
    have hp : val WuPaper.ClassicalFourthData.Bq 1683 = (145072767198222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1683 = 145072767198222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1683 = (9683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1684) ≤ val WuPaper.ClassicalFourthData.Bq 1684
    have hp : val WuPaper.ClassicalFourthData.Bq 1684 = (145130462253187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1684 = 145130462253187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1684 = (2421:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1685) ≤ val WuPaper.ClassicalFourthData.Bq 1685
    have hp : val WuPaper.ClassicalFourthData.Bq 1685 = (145188132610267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1685 = 145188132610267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1685 = (1937:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1686) ≤ val WuPaper.ClassicalFourthData.Bq 1686
    have hp : val WuPaper.ClassicalFourthData.Bq 1686 = (145245778281610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1686 = 145245778281610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1686 = (4843:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1687) ≤ val WuPaper.ClassicalFourthData.Bq 1687
    have hp : val WuPaper.ClassicalFourthData.Bq 1687 = (145303399279353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1687 = 145303399279353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1687 = (9687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1687
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1688) ≤ val WuPaper.ClassicalFourthData.Bq 1688
    have hp : val WuPaper.ClassicalFourthData.Bq 1688 = (145360995615628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1688 = 145360995615628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1688 = (1211:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1689) ≤ val WuPaper.ClassicalFourthData.Bq 1689
    have hp : val WuPaper.ClassicalFourthData.Bq 1689 = (145418567302558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1689 = 145418567302558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1689 = (9689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1690) ≤ val WuPaper.ClassicalFourthData.Bq 1690
    have hp : val WuPaper.ClassicalFourthData.Bq 1690 = (145476114352260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1690 = 145476114352260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1690 = (969:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1691) ≤ val WuPaper.ClassicalFourthData.Bq 1691
    have hp : val WuPaper.ClassicalFourthData.Bq 1691 = (145533636776843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1691 = 145533636776843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1691 = (9691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1692) ≤ val WuPaper.ClassicalFourthData.Bq 1692
    have hp : val WuPaper.ClassicalFourthData.Bq 1692 = (145591134588410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1692 = 145591134588410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1692 = (2423:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1693) ≤ val WuPaper.ClassicalFourthData.Bq 1693
    have hp : val WuPaper.ClassicalFourthData.Bq 1693 = (145648607799053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1693 = 145648607799053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1693 = (9693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1694) ≤ val WuPaper.ClassicalFourthData.Bq 1694
    have hp : val WuPaper.ClassicalFourthData.Bq 1694 = (145706056420861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1694 = 145706056420861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1694 = (4847:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1695) ≤ val WuPaper.ClassicalFourthData.Bq 1695
    have hp : val WuPaper.ClassicalFourthData.Bq 1695 = (145763480465913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1695 = 145763480465913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1695 = (1939:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_105
