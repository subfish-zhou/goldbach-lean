import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints113
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_113 (j : Fin 16) (hj : 16*113+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*113+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*113+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1808) ≤ val WuPaper.ClassicalFourthData.Bq 1808
    have hp : val WuPaper.ClassicalFourthData.Bq 1808 = (152097029527979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1808 = 152097029527979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1808 = (613:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1809) ≤ val WuPaper.ClassicalFourthData.Bq 1809
    have hp : val WuPaper.ClassicalFourthData.Bq 1809 = (152151729183609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1809 = 152151729183609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1809 = (9809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1810) ≤ val WuPaper.ClassicalFourthData.Bq 1810
    have hp : val WuPaper.ClassicalFourthData.Bq 1810 = (152206405604049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1810 = 152206405604049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1810 = (981:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1811) ≤ val WuPaper.ClassicalFourthData.Bq 1811
    have hp : val WuPaper.ClassicalFourthData.Bq 1811 = (152261058800562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1811 = 152261058800562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1811 = (9811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1812) ≤ val WuPaper.ClassicalFourthData.Bq 1812
    have hp : val WuPaper.ClassicalFourthData.Bq 1812 = (152315688784406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1812 = 152315688784406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1812 = (2453:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1813) ≤ val WuPaper.ClassicalFourthData.Bq 1813
    have hp : val WuPaper.ClassicalFourthData.Bq 1813 = (152370295566829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1813 = 152370295566829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1813 = (9813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1814) ≤ val WuPaper.ClassicalFourthData.Bq 1814
    have hp : val WuPaper.ClassicalFourthData.Bq 1814 = (152424879159077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1814 = 152424879159077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1814 = (4907:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1815) ≤ val WuPaper.ClassicalFourthData.Bq 1815
    have hp : val WuPaper.ClassicalFourthData.Bq 1815 = (152479439572384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1815 = 152479439572384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1815 = (1963:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1815
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1816) ≤ val WuPaper.ClassicalFourthData.Bq 1816
    have hp : val WuPaper.ClassicalFourthData.Bq 1816 = (152533976817982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1816 = 152533976817982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1816 = (1227:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1817) ≤ val WuPaper.ClassicalFourthData.Bq 1817
    have hp : val WuPaper.ClassicalFourthData.Bq 1817 = (152588490907094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1817 = 152588490907094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1817 = (9817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1818) ≤ val WuPaper.ClassicalFourthData.Bq 1818
    have hp : val WuPaper.ClassicalFourthData.Bq 1818 = (152642981850935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1818 = 152642981850935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1818 = (4909:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1819) ≤ val WuPaper.ClassicalFourthData.Bq 1819
    have hp : val WuPaper.ClassicalFourthData.Bq 1819 = (152697449660716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1819 = 152697449660716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1819 = (9819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1820) ≤ val WuPaper.ClassicalFourthData.Bq 1820
    have hp : val WuPaper.ClassicalFourthData.Bq 1820 = (152751894347640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1820 = 152751894347640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1820 = (491:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1821) ≤ val WuPaper.ClassicalFourthData.Bq 1821
    have hp : val WuPaper.ClassicalFourthData.Bq 1821 = (152806315922904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1821 = 152806315922904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1821 = (9821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1822) ≤ val WuPaper.ClassicalFourthData.Bq 1822
    have hp : val WuPaper.ClassicalFourthData.Bq 1822 = (152860714397696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1822 = 152860714397696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1822 = (4911:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1823) ≤ val WuPaper.ClassicalFourthData.Bq 1823
    have hp : val WuPaper.ClassicalFourthData.Bq 1823 = (152915089783200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1823 = 152915089783200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1823 = (9823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_113
