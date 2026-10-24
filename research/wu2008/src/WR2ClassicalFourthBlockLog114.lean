import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints114
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_114 (j : Fin 16) (hj : 16*114+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*114+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*114+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1824) ≤ val WuPaper.ClassicalFourthData.Bq 1824
    have hp : val WuPaper.ClassicalFourthData.Bq 1824 = (152969442090593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1824 = 152969442090593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1824 = (307:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1825) ≤ val WuPaper.ClassicalFourthData.Bq 1825
    have hp : val WuPaper.ClassicalFourthData.Bq 1825 = (153023771331043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1825 = 153023771331043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1825 = (393:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1826) ≤ val WuPaper.ClassicalFourthData.Bq 1826
    have hp : val WuPaper.ClassicalFourthData.Bq 1826 = (153078077515715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1826 = 153078077515715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1826 = (4913:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1827) ≤ val WuPaper.ClassicalFourthData.Bq 1827
    have hp : val WuPaper.ClassicalFourthData.Bq 1827 = (153132360655764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1827 = 153132360655764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1827 = (9827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1828) ≤ val WuPaper.ClassicalFourthData.Bq 1828
    have hp : val WuPaper.ClassicalFourthData.Bq 1828 = (153186620762340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1828 = 153186620762340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1828 = (2457:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1829) ≤ val WuPaper.ClassicalFourthData.Bq 1829
    have hp : val WuPaper.ClassicalFourthData.Bq 1829 = (153240857846586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1829 = 153240857846586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1829 = (9829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1830) ≤ val WuPaper.ClassicalFourthData.Bq 1830
    have hp : val WuPaper.ClassicalFourthData.Bq 1830 = (153295071919639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1830 = 153295071919639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1830 = (983:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1831) ≤ val WuPaper.ClassicalFourthData.Bq 1831
    have hp : val WuPaper.ClassicalFourthData.Bq 1831 = (153349262992627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1831 = 153349262992627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1831 = (9831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1831
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1832) ≤ val WuPaper.ClassicalFourthData.Bq 1832
    have hp : val WuPaper.ClassicalFourthData.Bq 1832 = (153403431076675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1832 = 153403431076675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1832 = (1229:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1833) ≤ val WuPaper.ClassicalFourthData.Bq 1833
    have hp : val WuPaper.ClassicalFourthData.Bq 1833 = (153457576182899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1833 = 153457576182899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1833 = (9833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1834) ≤ val WuPaper.ClassicalFourthData.Bq 1834
    have hp : val WuPaper.ClassicalFourthData.Bq 1834 = (153511698322408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1834 = 153511698322408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1834 = (4917:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1835) ≤ val WuPaper.ClassicalFourthData.Bq 1835
    have hp : val WuPaper.ClassicalFourthData.Bq 1835 = (153565797506306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1835 = 153565797506306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1835 = (1967:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1836) ≤ val WuPaper.ClassicalFourthData.Bq 1836
    have hp : val WuPaper.ClassicalFourthData.Bq 1836 = (153619873745689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1836 = 153619873745689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1836 = (2459:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1837) ≤ val WuPaper.ClassicalFourthData.Bq 1837
    have hp : val WuPaper.ClassicalFourthData.Bq 1837 = (153673927051648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1837 = 153673927051648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1837 = (9837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1838) ≤ val WuPaper.ClassicalFourthData.Bq 1838
    have hp : val WuPaper.ClassicalFourthData.Bq 1838 = (153727957435265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1838 = 153727957435265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1838 = (4919:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1839) ≤ val WuPaper.ClassicalFourthData.Bq 1839
    have hp : val WuPaper.ClassicalFourthData.Bq 1839 = (153781964907617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1839 = 153781964907617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1839 = (9839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_114
