import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints119
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_119 (j : Fin 16) (hj : 16*119+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*119+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*119+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1904) ≤ val WuPaper.ClassicalFourthData.Bq 1904
    have hp : val WuPaper.ClassicalFourthData.Bq 1904 = (157243831251326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1904 = 157243831251326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1904 = (619:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1905) ≤ val WuPaper.ClassicalFourthData.Bq 1905
    have hp : val WuPaper.ClassicalFourthData.Bq 1905 = (157296350743841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1905 = 157296350743841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1905 = (1981:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1906) ≤ val WuPaper.ClassicalFourthData.Bq 1906
    have hp : val WuPaper.ClassicalFourthData.Bq 1906 = (157348848052429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1906 = 157348848052429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1906 = (4953:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1907) ≤ val WuPaper.ClassicalFourthData.Bq 1907
    have hp : val WuPaper.ClassicalFourthData.Bq 1907 = (157401323187729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1907 = 157401323187729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1907 = (9907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1908) ≤ val WuPaper.ClassicalFourthData.Bq 1908
    have hp : val WuPaper.ClassicalFourthData.Bq 1908 = (157453776160373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1908 = 157453776160373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1908 = (2477:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1909) ≤ val WuPaper.ClassicalFourthData.Bq 1909
    have hp : val WuPaper.ClassicalFourthData.Bq 1909 = (157506206980986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1909 = 157506206980986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1909 = (9909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1910) ≤ val WuPaper.ClassicalFourthData.Bq 1910
    have hp : val WuPaper.ClassicalFourthData.Bq 1910 = (157558615660189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1910 = 157558615660189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1910 = (991:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1911) ≤ val WuPaper.ClassicalFourthData.Bq 1911
    have hp : val WuPaper.ClassicalFourthData.Bq 1911 = (157611002208594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1911 = 157611002208594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1911 = (9911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1911
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1912) ≤ val WuPaper.ClassicalFourthData.Bq 1912
    have hp : val WuPaper.ClassicalFourthData.Bq 1912 = (157663366636808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1912 = 157663366636808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1912 = (1239:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1913) ≤ val WuPaper.ClassicalFourthData.Bq 1913
    have hp : val WuPaper.ClassicalFourthData.Bq 1913 = (157715708955434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1913 = 157715708955434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1913 = (9913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1914) ≤ val WuPaper.ClassicalFourthData.Bq 1914
    have hp : val WuPaper.ClassicalFourthData.Bq 1914 = (157768029175064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1914 = 157768029175064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1914 = (4957:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1915) ≤ val WuPaper.ClassicalFourthData.Bq 1915
    have hp : val WuPaper.ClassicalFourthData.Bq 1915 = (157820327306288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1915 = 157820327306288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1915 = (1983:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1916) ≤ val WuPaper.ClassicalFourthData.Bq 1916
    have hp : val WuPaper.ClassicalFourthData.Bq 1916 = (157872603359687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1916 = 157872603359687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1916 = (2479:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1917) ≤ val WuPaper.ClassicalFourthData.Bq 1917
    have hp : val WuPaper.ClassicalFourthData.Bq 1917 = (157924857345838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1917 = 157924857345838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1917 = (9917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1918) ≤ val WuPaper.ClassicalFourthData.Bq 1918
    have hp : val WuPaper.ClassicalFourthData.Bq 1918 = (157977089275309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1918 = 157977089275309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1918 = (4959:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1919) ≤ val WuPaper.ClassicalFourthData.Bq 1919
    have hp : val WuPaper.ClassicalFourthData.Bq 1919 = (158029299158665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1919 = 158029299158665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1919 = (9919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_119
