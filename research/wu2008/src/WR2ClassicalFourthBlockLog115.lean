import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints115
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_115 (j : Fin 16) (hj : 16*115+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*115+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*115+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1840) ≤ val WuPaper.ClassicalFourthData.Bq 1840
    have hp : val WuPaper.ClassicalFourthData.Bq 1840 = (153835949479775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1840 = 153835949479775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1840 = (123:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1841) ≤ val WuPaper.ClassicalFourthData.Bq 1841
    have hp : val WuPaper.ClassicalFourthData.Bq 1841 = (153889911162802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1841 = 153889911162802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1841 = (9841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1842) ≤ val WuPaper.ClassicalFourthData.Bq 1842
    have hp : val WuPaper.ClassicalFourthData.Bq 1842 = (153943849967754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1842 = 153943849967754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1842 = (4921:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1843) ≤ val WuPaper.ClassicalFourthData.Bq 1843
    have hp : val WuPaper.ClassicalFourthData.Bq 1843 = (153997765905683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1843 = 153997765905683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1843 = (9843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1844) ≤ val WuPaper.ClassicalFourthData.Bq 1844
    have hp : val WuPaper.ClassicalFourthData.Bq 1844 = (154051658987633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1844 = 154051658987633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1844 = (2461:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1845) ≤ val WuPaper.ClassicalFourthData.Bq 1845
    have hp : val WuPaper.ClassicalFourthData.Bq 1845 = (154105529224639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1845 = 154105529224639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1845 = (1969:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1846) ≤ val WuPaper.ClassicalFourthData.Bq 1846
    have hp : val WuPaper.ClassicalFourthData.Bq 1846 = (154159376627733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1846 = 154159376627733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1846 = (4923:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1847) ≤ val WuPaper.ClassicalFourthData.Bq 1847
    have hp : val WuPaper.ClassicalFourthData.Bq 1847 = (154213201207939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1847 = 154213201207939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1847 = (9847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1847
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1848) ≤ val WuPaper.ClassicalFourthData.Bq 1848
    have hp : val WuPaper.ClassicalFourthData.Bq 1848 = (154267002976275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1848 = 154267002976275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1848 = (1231:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1849) ≤ val WuPaper.ClassicalFourthData.Bq 1849
    have hp : val WuPaper.ClassicalFourthData.Bq 1849 = (154320781943750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1849 = 154320781943750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1849 = (9849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1850) ≤ val WuPaper.ClassicalFourthData.Bq 1850
    have hp : val WuPaper.ClassicalFourthData.Bq 1850 = (154374538121371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1850 = 154374538121371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1850 = (197:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1851) ≤ val WuPaper.ClassicalFourthData.Bq 1851
    have hp : val WuPaper.ClassicalFourthData.Bq 1851 = (154428271520134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1851 = 154428271520134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1851 = (9851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1852) ≤ val WuPaper.ClassicalFourthData.Bq 1852
    have hp : val WuPaper.ClassicalFourthData.Bq 1852 = (154481982151031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1852 = 154481982151031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1852 = (2463:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1853) ≤ val WuPaper.ClassicalFourthData.Bq 1853
    have hp : val WuPaper.ClassicalFourthData.Bq 1853 = (154535670025046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1853 = 154535670025046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1853 = (9853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1854) ≤ val WuPaper.ClassicalFourthData.Bq 1854
    have hp : val WuPaper.ClassicalFourthData.Bq 1854 = (154589335153158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1854 = 154589335153158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1854 = (4927:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1855) ≤ val WuPaper.ClassicalFourthData.Bq 1855
    have hp : val WuPaper.ClassicalFourthData.Bq 1855 = (154642977546338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1855 = 154642977546338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1855 = (1971:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_115
