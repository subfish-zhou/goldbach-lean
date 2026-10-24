import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints486
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_486 (j : Fin 16) (hj : 16*486+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*486+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*486+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7776) ≤ val WuPaper.ClassicalFourthData.Bq 7776
    have hp : val WuPaper.ClassicalFourthData.Bq 7776 = (273775152349952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7776 = 273775152349952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7776 = (493:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7777) ≤ val WuPaper.ClassicalFourthData.Bq 7777
    have hp : val WuPaper.ClassicalFourthData.Bq 7777 = (273779328323789:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7777 = 273779328323789 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7777 = (15777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7778) ≤ val WuPaper.ClassicalFourthData.Bq 7778
    have hp : val WuPaper.ClassicalFourthData.Bq 7778 = (273783501940442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7778 = 273783501940442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7778 = (7889:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7779) ≤ val WuPaper.ClassicalFourthData.Bq 7779
    have hp : val WuPaper.ClassicalFourthData.Bq 7779 = (273787673200671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7779 = 273787673200671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7779 = (15779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7780) ≤ val WuPaper.ClassicalFourthData.Bq 7780
    have hp : val WuPaper.ClassicalFourthData.Bq 7780 = (273791842105233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7780 = 273791842105233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7780 = (789:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7781) ≤ val WuPaper.ClassicalFourthData.Bq 7781
    have hp : val WuPaper.ClassicalFourthData.Bq 7781 = (273796008654886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7781 = 273796008654886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7781 = (15781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7782) ≤ val WuPaper.ClassicalFourthData.Bq 7782
    have hp : val WuPaper.ClassicalFourthData.Bq 7782 = (273800172850388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7782 = 273800172850388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7782 = (7891:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7783) ≤ val WuPaper.ClassicalFourthData.Bq 7783
    have hp : val WuPaper.ClassicalFourthData.Bq 7783 = (273804334692496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7783 = 273804334692496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7783 = (15783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7783
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7784) ≤ val WuPaper.ClassicalFourthData.Bq 7784
    have hp : val WuPaper.ClassicalFourthData.Bq 7784 = (273808494181968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7784 = 273808494181968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7784 = (1973:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7785) ≤ val WuPaper.ClassicalFourthData.Bq 7785
    have hp : val WuPaper.ClassicalFourthData.Bq 7785 = (273812651319560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7785 = 273812651319560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7785 = (3157:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7786) ≤ val WuPaper.ClassicalFourthData.Bq 7786
    have hp : val WuPaper.ClassicalFourthData.Bq 7786 = (273816806106030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7786 = 273816806106030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7786 = (7893:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7787) ≤ val WuPaper.ClassicalFourthData.Bq 7787
    have hp : val WuPaper.ClassicalFourthData.Bq 7787 = (273820958542132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7787 = 273820958542132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7787 = (15787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7788) ≤ val WuPaper.ClassicalFourthData.Bq 7788
    have hp : val WuPaper.ClassicalFourthData.Bq 7788 = (273825108628624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7788 = 273825108628624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7788 = (3947:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7789) ≤ val WuPaper.ClassicalFourthData.Bq 7789
    have hp : val WuPaper.ClassicalFourthData.Bq 7789 = (273829256366261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7789 = 273829256366261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7789 = (15789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7790) ≤ val WuPaper.ClassicalFourthData.Bq 7790
    have hp : val WuPaper.ClassicalFourthData.Bq 7790 = (273833401755799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7790 = 273833401755799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7790 = (1579:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7791) ≤ val WuPaper.ClassicalFourthData.Bq 7791
    have hp : val WuPaper.ClassicalFourthData.Bq 7791 = (273837544797993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7791 = 273837544797993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7791 = (15791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_486
