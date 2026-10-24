import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints120
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_120 (j : Fin 16) (hj : 16*120+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*120+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*120+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1920) ≤ val WuPaper.ClassicalFourthData.Bq 1920
    have hp : val WuPaper.ClassicalFourthData.Bq 1920 = (158081487006462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1920 = 158081487006462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1920 = (62:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1921) ≤ val WuPaper.ClassicalFourthData.Bq 1921
    have hp : val WuPaper.ClassicalFourthData.Bq 1921 = (158133652829251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1921 = 158133652829251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1921 = (9921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1922) ≤ val WuPaper.ClassicalFourthData.Bq 1922
    have hp : val WuPaper.ClassicalFourthData.Bq 1922 = (158185796637577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1922 = 158185796637577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1922 = (4961:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1923) ≤ val WuPaper.ClassicalFourthData.Bq 1923
    have hp : val WuPaper.ClassicalFourthData.Bq 1923 = (158237918441979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1923 = 158237918441979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1923 = (9923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1924) ≤ val WuPaper.ClassicalFourthData.Bq 1924
    have hp : val WuPaper.ClassicalFourthData.Bq 1924 = (158290018252988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1924 = 158290018252988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1924 = (2481:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1925) ≤ val WuPaper.ClassicalFourthData.Bq 1925
    have hp : val WuPaper.ClassicalFourthData.Bq 1925 = (158342096081131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1925 = 158342096081131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1925 = (397:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1926) ≤ val WuPaper.ClassicalFourthData.Bq 1926
    have hp : val WuPaper.ClassicalFourthData.Bq 1926 = (158394151936927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1926 = 158394151936927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1926 = (4963:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1927) ≤ val WuPaper.ClassicalFourthData.Bq 1927
    have hp : val WuPaper.ClassicalFourthData.Bq 1927 = (158446185830890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1927 = 158446185830890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1927 = (9927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1927
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1928) ≤ val WuPaper.ClassicalFourthData.Bq 1928
    have hp : val WuPaper.ClassicalFourthData.Bq 1928 = (158498197773528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1928 = 158498197773528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1928 = (1241:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1929) ≤ val WuPaper.ClassicalFourthData.Bq 1929
    have hp : val WuPaper.ClassicalFourthData.Bq 1929 = (158550187775341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1929 = 158550187775341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1929 = (9929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1930) ≤ val WuPaper.ClassicalFourthData.Bq 1930
    have hp : val WuPaper.ClassicalFourthData.Bq 1930 = (158602155846826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1930 = 158602155846826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1930 = (993:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1931) ≤ val WuPaper.ClassicalFourthData.Bq 1931
    have hp : val WuPaper.ClassicalFourthData.Bq 1931 = (158654101998470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1931 = 158654101998470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1931 = (9931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1932) ≤ val WuPaper.ClassicalFourthData.Bq 1932
    have hp : val WuPaper.ClassicalFourthData.Bq 1932 = (158706026240756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1932 = 158706026240756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1932 = (2483:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1933) ≤ val WuPaper.ClassicalFourthData.Bq 1933
    have hp : val WuPaper.ClassicalFourthData.Bq 1933 = (158757928584161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1933 = 158757928584161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1933 = (9933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1934) ≤ val WuPaper.ClassicalFourthData.Bq 1934
    have hp : val WuPaper.ClassicalFourthData.Bq 1934 = (158809809039155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1934 = 158809809039155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1934 = (4967:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1935) ≤ val WuPaper.ClassicalFourthData.Bq 1935
    have hp : val WuPaper.ClassicalFourthData.Bq 1935 = (158861667616202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1935 = 158861667616202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1935 = (1987:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_120
