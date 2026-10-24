import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints254
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_254 (j : Fin 16) (hj : 16*254+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*254+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*254+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4064) ≤ val WuPaper.ClassicalFourthData.Bq 4064
    have hp : val WuPaper.ClassicalFourthData.Bq 4064 = (232465301793476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4064 = 232465301793476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4064 = (377:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4065) ≤ val WuPaper.ClassicalFourthData.Bq 4065
    have hp : val WuPaper.ClassicalFourthData.Bq 4065 = (232487144784843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4065 = 232487144784843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4065 = (2413:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4066) ≤ val WuPaper.ClassicalFourthData.Bq 4066
    have hp : val WuPaper.ClassicalFourthData.Bq 4066 = (232508979058938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4066 = 232508979058938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4066 = (6033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4067) ≤ val WuPaper.ClassicalFourthData.Bq 4067
    have hp : val WuPaper.ClassicalFourthData.Bq 4067 = (232530804619192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4067 = 232530804619192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4067 = (12067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4068) ≤ val WuPaper.ClassicalFourthData.Bq 4068
    have hp : val WuPaper.ClassicalFourthData.Bq 4068 = (232552621469034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4068 = 232552621469034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4068 = (3017:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4069) ≤ val WuPaper.ClassicalFourthData.Bq 4069
    have hp : val WuPaper.ClassicalFourthData.Bq 4069 = (232574429611892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4069 = 232574429611892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4069 = (12069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4070) ≤ val WuPaper.ClassicalFourthData.Bq 4070
    have hp : val WuPaper.ClassicalFourthData.Bq 4070 = (232596229051191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4070 = 232596229051191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4070 = (1207:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4071) ≤ val WuPaper.ClassicalFourthData.Bq 4071
    have hp : val WuPaper.ClassicalFourthData.Bq 4071 = (232618019790356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4071 = 232618019790356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4071 = (12071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4071
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4072) ≤ val WuPaper.ClassicalFourthData.Bq 4072
    have hp : val WuPaper.ClassicalFourthData.Bq 4072 = (232639801832809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4072 = 232639801832809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4072 = (1509:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4073) ≤ val WuPaper.ClassicalFourthData.Bq 4073
    have hp : val WuPaper.ClassicalFourthData.Bq 4073 = (232661575181973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4073 = 232661575181973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4073 = (12073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4074) ≤ val WuPaper.ClassicalFourthData.Bq 4074
    have hp : val WuPaper.ClassicalFourthData.Bq 4074 = (232683339841266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4074 = 232683339841266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4074 = (6037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4075) ≤ val WuPaper.ClassicalFourthData.Bq 4075
    have hp : val WuPaper.ClassicalFourthData.Bq 4075 = (232705095814106:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4075 = 232705095814106 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4075 = (483:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4076) ≤ val WuPaper.ClassicalFourthData.Bq 4076
    have hp : val WuPaper.ClassicalFourthData.Bq 4076 = (232726843103909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4076 = 232726843103909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4076 = (3019:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4077) ≤ val WuPaper.ClassicalFourthData.Bq 4077
    have hp : val WuPaper.ClassicalFourthData.Bq 4077 = (232748581714091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4077 = 232748581714091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4077 = (12077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4078) ≤ val WuPaper.ClassicalFourthData.Bq 4078
    have hp : val WuPaper.ClassicalFourthData.Bq 4078 = (232770311648065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4078 = 232770311648065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4078 = (6039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4079) ≤ val WuPaper.ClassicalFourthData.Bq 4079
    have hp : val WuPaper.ClassicalFourthData.Bq 4079 = (232792032909242:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4079 = 232792032909242 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4079 = (12079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_254
