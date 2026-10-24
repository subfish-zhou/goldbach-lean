import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints116
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_116 (j : Fin 16) (hj : 16*116+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*116+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*116+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1856) ≤ val WuPaper.ClassicalFourthData.Bq 1856
    have hp : val WuPaper.ClassicalFourthData.Bq 1856 = (154696597215552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1856 = 154696597215552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1856 = (308:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1857) ≤ val WuPaper.ClassicalFourthData.Bq 1857
    have hp : val WuPaper.ClassicalFourthData.Bq 1857 = (154750194171758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1857 = 154750194171758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1857 = (9857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1858) ≤ val WuPaper.ClassicalFourthData.Bq 1858
    have hp : val WuPaper.ClassicalFourthData.Bq 1858 = (154803768425909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1858 = 154803768425909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1858 = (4929:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1859) ≤ val WuPaper.ClassicalFourthData.Bq 1859
    have hp : val WuPaper.ClassicalFourthData.Bq 1859 = (154857319988949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1859 = 154857319988949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1859 = (9859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1860) ≤ val WuPaper.ClassicalFourthData.Bq 1860
    have hp : val WuPaper.ClassicalFourthData.Bq 1860 = (154910848871818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1860 = 154910848871818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1860 = (493:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1861) ≤ val WuPaper.ClassicalFourthData.Bq 1861
    have hp : val WuPaper.ClassicalFourthData.Bq 1861 = (154964355085449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1861 = 154964355085449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1861 = (9861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1862) ≤ val WuPaper.ClassicalFourthData.Bq 1862
    have hp : val WuPaper.ClassicalFourthData.Bq 1862 = (155017838640767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1862 = 155017838640767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1862 = (4931:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1863) ≤ val WuPaper.ClassicalFourthData.Bq 1863
    have hp : val WuPaper.ClassicalFourthData.Bq 1863 = (155071299548693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1863 = 155071299548693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1863 = (9863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1863
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1864) ≤ val WuPaper.ClassicalFourthData.Bq 1864
    have hp : val WuPaper.ClassicalFourthData.Bq 1864 = (155124737820138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1864 = 155124737820138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1864 = (1233:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1865) ≤ val WuPaper.ClassicalFourthData.Bq 1865
    have hp : val WuPaper.ClassicalFourthData.Bq 1865 = (155178153466011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1865 = 155178153466011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1865 = (1973:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1866) ≤ val WuPaper.ClassicalFourthData.Bq 1866
    have hp : val WuPaper.ClassicalFourthData.Bq 1866 = (155231546497211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1866 = 155231546497211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1866 = (4933:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1867) ≤ val WuPaper.ClassicalFourthData.Bq 1867
    have hp : val WuPaper.ClassicalFourthData.Bq 1867 = (155284916924631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1867 = 155284916924631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1867 = (9867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1868) ≤ val WuPaper.ClassicalFourthData.Bq 1868
    have hp : val WuPaper.ClassicalFourthData.Bq 1868 = (155338264759159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1868 = 155338264759159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1868 = (2467:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1869) ≤ val WuPaper.ClassicalFourthData.Bq 1869
    have hp : val WuPaper.ClassicalFourthData.Bq 1869 = (155391590011676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1869 = 155391590011676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1869 = (9869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1870) ≤ val WuPaper.ClassicalFourthData.Bq 1870
    have hp : val WuPaper.ClassicalFourthData.Bq 1870 = (155444892693056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1870 = 155444892693056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1870 = (987:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1871) ≤ val WuPaper.ClassicalFourthData.Bq 1871
    have hp : val WuPaper.ClassicalFourthData.Bq 1871 = (155498172814167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1871 = 155498172814167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1871 = (9871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_116
