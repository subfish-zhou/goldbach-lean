import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints627
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_627 (j : Fin 16) (hj : 16*627+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*627+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*627+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10032) ≤ val WuPaper.ClassicalFourthData.Bq 10032
    have hp : val WuPaper.ClassicalFourthData.Bq 10032 = (278404186914379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10032 = 278404186914379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10032 = (1127:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10033) ≤ val WuPaper.ClassicalFourthData.Bq 10033
    have hp : val WuPaper.ClassicalFourthData.Bq 10033 = (278404555592380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10033 = 278404555592380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10033 = (18033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10034) ≤ val WuPaper.ClassicalFourthData.Bq 10034
    have hp : val WuPaper.ClassicalFourthData.Bq 10034 = (278404923103161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10034 = 278404923103161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10034 = (9017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10035) ≤ val WuPaper.ClassicalFourthData.Bq 10035
    have hp : val WuPaper.ClassicalFourthData.Bq 10035 = (278405289447076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10035 = 278405289447076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10035 = (3607:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10036) ≤ val WuPaper.ClassicalFourthData.Bq 10036
    have hp : val WuPaper.ClassicalFourthData.Bq 10036 = (278405654624481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10036 = 278405654624481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10036 = (4509:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10037) ≤ val WuPaper.ClassicalFourthData.Bq 10037
    have hp : val WuPaper.ClassicalFourthData.Bq 10037 = (278406018635729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10037 = 278406018635729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10037 = (18037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10038) ≤ val WuPaper.ClassicalFourthData.Bq 10038
    have hp : val WuPaper.ClassicalFourthData.Bq 10038 = (278406381481175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10038 = 278406381481175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10038 = (9019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10039) ≤ val WuPaper.ClassicalFourthData.Bq 10039
    have hp : val WuPaper.ClassicalFourthData.Bq 10039 = (278406743161173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10039 = 278406743161173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10039 = (18039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10039
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10040) ≤ val WuPaper.ClassicalFourthData.Bq 10040
    have hp : val WuPaper.ClassicalFourthData.Bq 10040 = (278407103676077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10040 = 278407103676077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10040 = (451:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10041) ≤ val WuPaper.ClassicalFourthData.Bq 10041
    have hp : val WuPaper.ClassicalFourthData.Bq 10041 = (278407463026241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10041 = 278407463026241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10041 = (18041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10042) ≤ val WuPaper.ClassicalFourthData.Bq 10042
    have hp : val WuPaper.ClassicalFourthData.Bq 10042 = (278407821212020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10042 = 278407821212020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10042 = (9021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10043) ≤ val WuPaper.ClassicalFourthData.Bq 10043
    have hp : val WuPaper.ClassicalFourthData.Bq 10043 = (278408178233766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10043 = 278408178233766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10043 = (18043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10044) ≤ val WuPaper.ClassicalFourthData.Bq 10044
    have hp : val WuPaper.ClassicalFourthData.Bq 10044 = (278408534091833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10044 = 278408534091833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10044 = (4511:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10045) ≤ val WuPaper.ClassicalFourthData.Bq 10045
    have hp : val WuPaper.ClassicalFourthData.Bq 10045 = (278408888786576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10045 = 278408888786576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10045 = (3609:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10046) ≤ val WuPaper.ClassicalFourthData.Bq 10046
    have hp : val WuPaper.ClassicalFourthData.Bq 10046 = (278409242318346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10046 = 278409242318346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10046 = (9023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10047) ≤ val WuPaper.ClassicalFourthData.Bq 10047
    have hp : val WuPaper.ClassicalFourthData.Bq 10047 = (278409594687499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10047 = 278409594687499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10047 = (18047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_627
