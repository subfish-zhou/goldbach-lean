import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints111
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_111 (j : Fin 16) (hj : 16*111+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*111+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*111+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1776) ≤ val WuPaper.ClassicalFourthData.Bq 1776
    have hp : val WuPaper.ClassicalFourthData.Bq 1776 = (150334304611553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1776 = 150334304611553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1776 = (611:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1777) ≤ val WuPaper.ClassicalFourthData.Bq 1777
    have hp : val WuPaper.ClassicalFourthData.Bq 1777 = (150389753781012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1777 = 150389753781012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1777 = (9777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1778) ≤ val WuPaper.ClassicalFourthData.Bq 1778
    have hp : val WuPaper.ClassicalFourthData.Bq 1778 = (150445179351260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1778 = 150445179351260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1778 = (4889:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1779) ≤ val WuPaper.ClassicalFourthData.Bq 1779
    have hp : val WuPaper.ClassicalFourthData.Bq 1779 = (150500581333777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1779 = 150500581333777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1779 = (9779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1780) ≤ val WuPaper.ClassicalFourthData.Bq 1780
    have hp : val WuPaper.ClassicalFourthData.Bq 1780 = (150555959740040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1780 = 150555959740040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1780 = (489:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1781) ≤ val WuPaper.ClassicalFourthData.Bq 1781
    have hp : val WuPaper.ClassicalFourthData.Bq 1781 = (150611314581515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1781 = 150611314581515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1781 = (9781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1782) ≤ val WuPaper.ClassicalFourthData.Bq 1782
    have hp : val WuPaper.ClassicalFourthData.Bq 1782 = (150666645869665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1782 = 150666645869665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1782 = (4891:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1783) ≤ val WuPaper.ClassicalFourthData.Bq 1783
    have hp : val WuPaper.ClassicalFourthData.Bq 1783 = (150721953615943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1783 = 150721953615943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1783 = (9783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1783
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1784) ≤ val WuPaper.ClassicalFourthData.Bq 1784
    have hp : val WuPaper.ClassicalFourthData.Bq 1784 = (150777237831796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1784 = 150777237831796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1784 = (1223:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1785) ≤ val WuPaper.ClassicalFourthData.Bq 1785
    have hp : val WuPaper.ClassicalFourthData.Bq 1785 = (150832498528667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1785 = 150832498528667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1785 = (1957:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1786) ≤ val WuPaper.ClassicalFourthData.Bq 1786
    have hp : val WuPaper.ClassicalFourthData.Bq 1786 = (150887735717986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1786 = 150887735717986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1786 = (4893:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1787) ≤ val WuPaper.ClassicalFourthData.Bq 1787
    have hp : val WuPaper.ClassicalFourthData.Bq 1787 = (150942949411183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1787 = 150942949411183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1787 = (9787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1788) ≤ val WuPaper.ClassicalFourthData.Bq 1788
    have hp : val WuPaper.ClassicalFourthData.Bq 1788 = (150998139619676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1788 = 150998139619676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1788 = (2447:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1789) ≤ val WuPaper.ClassicalFourthData.Bq 1789
    have hp : val WuPaper.ClassicalFourthData.Bq 1789 = (151053306354879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1789 = 151053306354879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1789 = (9789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1790) ≤ val WuPaper.ClassicalFourthData.Bq 1790
    have hp : val WuPaper.ClassicalFourthData.Bq 1790 = (151108449628198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1790 = 151108449628198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1790 = (979:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1791) ≤ val WuPaper.ClassicalFourthData.Bq 1791
    have hp : val WuPaper.ClassicalFourthData.Bq 1791 = (151163569451032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1791 = 151163569451032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1791 = (9791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1791
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_111
