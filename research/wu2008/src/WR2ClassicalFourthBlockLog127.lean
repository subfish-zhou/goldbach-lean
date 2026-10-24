import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints127
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_127 (j : Fin 16) (hj : 16*127+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*127+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*127+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2032) ≤ val WuPaper.ClassicalFourthData.Bq 2032
    have hp : val WuPaper.ClassicalFourthData.Bq 2032 = (163789581174548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2032 = 163789581174548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2032 = (627:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2033) ≤ val WuPaper.ClassicalFourthData.Bq 2033
    have hp : val WuPaper.ClassicalFourthData.Bq 2033 = (163839345495359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2033 = 163839345495359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2033 = (10033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2034) ≤ val WuPaper.ClassicalFourthData.Bq 2034
    have hp : val WuPaper.ClassicalFourthData.Bq 2034 = (163889088944381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2034 = 163889088944381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2034 = (5017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2035) ≤ val WuPaper.ClassicalFourthData.Bq 2035
    have hp : val WuPaper.ClassicalFourthData.Bq 2035 = (163938811531482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2035 = 163938811531482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2035 = (2007:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2036) ≤ val WuPaper.ClassicalFourthData.Bq 2036
    have hp : val WuPaper.ClassicalFourthData.Bq 2036 = (163988513266526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2036 = 163988513266526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2036 = (2509:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2037) ≤ val WuPaper.ClassicalFourthData.Bq 2037
    have hp : val WuPaper.ClassicalFourthData.Bq 2037 = (164038194159370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2037 = 164038194159370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2037 = (10037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2038) ≤ val WuPaper.ClassicalFourthData.Bq 2038
    have hp : val WuPaper.ClassicalFourthData.Bq 2038 = (164087854219868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2038 = 164087854219868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2038 = (5019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2039) ≤ val WuPaper.ClassicalFourthData.Bq 2039
    have hp : val WuPaper.ClassicalFourthData.Bq 2039 = (164137493457864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2039 = 164137493457864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2039 = (10039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2039
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2040) ≤ val WuPaper.ClassicalFourthData.Bq 2040
    have hp : val WuPaper.ClassicalFourthData.Bq 2040 = (164187111883201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2040 = 164187111883201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2040 = (251:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2041) ≤ val WuPaper.ClassicalFourthData.Bq 2041
    have hp : val WuPaper.ClassicalFourthData.Bq 2041 = (164236709505713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2041 = 164236709505713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2041 = (10041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2042) ≤ val WuPaper.ClassicalFourthData.Bq 2042
    have hp : val WuPaper.ClassicalFourthData.Bq 2042 = (164286286335228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2042 = 164286286335228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2042 = (5021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2043) ≤ val WuPaper.ClassicalFourthData.Bq 2043
    have hp : val WuPaper.ClassicalFourthData.Bq 2043 = (164335842381572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2043 = 164335842381572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2043 = (10043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2044) ≤ val WuPaper.ClassicalFourthData.Bq 2044
    have hp : val WuPaper.ClassicalFourthData.Bq 2044 = (164385377654561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2044 = 164385377654561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2044 = (2511:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2045) ≤ val WuPaper.ClassicalFourthData.Bq 2045
    have hp : val WuPaper.ClassicalFourthData.Bq 2045 = (164434892164009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2045 = 164434892164009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2045 = (2009:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2046) ≤ val WuPaper.ClassicalFourthData.Bq 2046
    have hp : val WuPaper.ClassicalFourthData.Bq 2046 = (164484385919720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2046 = 164484385919720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2046 = (5023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2047) ≤ val WuPaper.ClassicalFourthData.Bq 2047
    have hp : val WuPaper.ClassicalFourthData.Bq 2047 = (164533858931497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2047 = 164533858931497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2047 = (10047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_127
