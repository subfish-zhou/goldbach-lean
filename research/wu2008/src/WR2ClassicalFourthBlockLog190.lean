import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints190
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_190 (j : Fin 16) (hj : 16*190+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*190+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*190+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3040) ≤ val WuPaper.ClassicalFourthData.Bq 3040
    have hp : val WuPaper.ClassicalFourthData.Bq 3040 = (204823843858718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3040 = 204823843858718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3040 = (69:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3041) ≤ val WuPaper.ClassicalFourthData.Bq 3041
    have hp : val WuPaper.ClassicalFourthData.Bq 3041 = (204856750083183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3041 = 204856750083183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3041 = (11041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3042) ≤ val WuPaper.ClassicalFourthData.Bq 3042
    have hp : val WuPaper.ClassicalFourthData.Bq 3042 = (204889643040381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3042 = 204889643040381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3042 = (5521:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3043) ≤ val WuPaper.ClassicalFourthData.Bq 3043
    have hp : val WuPaper.ClassicalFourthData.Bq 3043 = (204922522735990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3043 = 204922522735990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3043 = (11043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3044) ≤ val WuPaper.ClassicalFourthData.Bq 3044
    have hp : val WuPaper.ClassicalFourthData.Bq 3044 = (204955389175687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3044 = 204955389175687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3044 = (2761:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3045) ≤ val WuPaper.ClassicalFourthData.Bq 3045
    have hp : val WuPaper.ClassicalFourthData.Bq 3045 = (204988242365144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3045 = 204988242365144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3045 = (2209:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3046) ≤ val WuPaper.ClassicalFourthData.Bq 3046
    have hp : val WuPaper.ClassicalFourthData.Bq 3046 = (205021082310033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3046 = 205021082310033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3046 = (5523:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3047) ≤ val WuPaper.ClassicalFourthData.Bq 3047
    have hp : val WuPaper.ClassicalFourthData.Bq 3047 = (205053909016021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3047 = 205053909016021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3047 = (11047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3047
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3048) ≤ val WuPaper.ClassicalFourthData.Bq 3048
    have hp : val WuPaper.ClassicalFourthData.Bq 3048 = (205086722488772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3048 = 205086722488772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3048 = (1381:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3049) ≤ val WuPaper.ClassicalFourthData.Bq 3049
    have hp : val WuPaper.ClassicalFourthData.Bq 3049 = (205119522733949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3049 = 205119522733949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3049 = (11049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3050) ≤ val WuPaper.ClassicalFourthData.Bq 3050
    have hp : val WuPaper.ClassicalFourthData.Bq 3050 = (205152309757208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3050 = 205152309757208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3050 = (221:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3051) ≤ val WuPaper.ClassicalFourthData.Bq 3051
    have hp : val WuPaper.ClassicalFourthData.Bq 3051 = (205185083564208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3051 = 205185083564208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3051 = (11051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3052) ≤ val WuPaper.ClassicalFourthData.Bq 3052
    have hp : val WuPaper.ClassicalFourthData.Bq 3052 = (205217844160599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3052 = 205217844160599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3052 = (2763:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3053) ≤ val WuPaper.ClassicalFourthData.Bq 3053
    have hp : val WuPaper.ClassicalFourthData.Bq 3053 = (205250591552032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3053 = 205250591552032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3053 = (11053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3054) ≤ val WuPaper.ClassicalFourthData.Bq 3054
    have hp : val WuPaper.ClassicalFourthData.Bq 3054 = (205283325744155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3054 = 205283325744155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3054 = (5527:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3055) ≤ val WuPaper.ClassicalFourthData.Bq 3055
    have hp : val WuPaper.ClassicalFourthData.Bq 3055 = (205316046742610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3055 = 205316046742610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3055 = (2211:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_190
