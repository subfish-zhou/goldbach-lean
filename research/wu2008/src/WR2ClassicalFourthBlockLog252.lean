import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints252
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_252 (j : Fin 16) (hj : 16*252+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*252+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*252+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4032) ≤ val WuPaper.ClassicalFourthData.Bq 4032
    have hp : val WuPaper.ClassicalFourthData.Bq 4032 = (231761702735866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4032 = 231761702735866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4032 = (376:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4033) ≤ val WuPaper.ClassicalFourthData.Bq 4033
    have hp : val WuPaper.ClassicalFourthData.Bq 4033 = (231783826501051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4033 = 231783826501051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4033 = (12033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4034) ≤ val WuPaper.ClassicalFourthData.Bq 4034
    have hp : val WuPaper.ClassicalFourthData.Bq 4034 = (231805941438325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4034 = 231805941438325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4034 = (6017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4035) ≤ val WuPaper.ClassicalFourthData.Bq 4035
    have hp : val WuPaper.ClassicalFourthData.Bq 4035 = (231828047551171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4035 = 231828047551171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4035 = (2407:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4036) ≤ val WuPaper.ClassicalFourthData.Bq 4036
    have hp : val WuPaper.ClassicalFourthData.Bq 4036 = (231850144843070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4036 = 231850144843070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4036 = (3009:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4037) ≤ val WuPaper.ClassicalFourthData.Bq 4037
    have hp : val WuPaper.ClassicalFourthData.Bq 4037 = (231872233317502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4037 = 231872233317502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4037 = (12037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4038) ≤ val WuPaper.ClassicalFourthData.Bq 4038
    have hp : val WuPaper.ClassicalFourthData.Bq 4038 = (231894312977943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4038 = 231894312977943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4038 = (6019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4039) ≤ val WuPaper.ClassicalFourthData.Bq 4039
    have hp : val WuPaper.ClassicalFourthData.Bq 4039 = (231916383827871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4039 = 231916383827871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4039 = (12039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4039
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4040) ≤ val WuPaper.ClassicalFourthData.Bq 4040
    have hp : val WuPaper.ClassicalFourthData.Bq 4040 = (231938445870759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4040 = 231938445870759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4040 = (301:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4041) ≤ val WuPaper.ClassicalFourthData.Bq 4041
    have hp : val WuPaper.ClassicalFourthData.Bq 4041 = (231960499110082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4041 = 231960499110082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4041 = (12041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4042) ≤ val WuPaper.ClassicalFourthData.Bq 4042
    have hp : val WuPaper.ClassicalFourthData.Bq 4042 = (231982543549308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4042 = 231982543549308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4042 = (6021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4043) ≤ val WuPaper.ClassicalFourthData.Bq 4043
    have hp : val WuPaper.ClassicalFourthData.Bq 4043 = (232004579191910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4043 = 232004579191910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4043 = (12043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4044) ≤ val WuPaper.ClassicalFourthData.Bq 4044
    have hp : val WuPaper.ClassicalFourthData.Bq 4044 = (232026606041354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4044 = 232026606041354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4044 = (3011:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4045) ≤ val WuPaper.ClassicalFourthData.Bq 4045
    have hp : val WuPaper.ClassicalFourthData.Bq 4045 = (232048624101107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4045 = 232048624101107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4045 = (2409:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4046) ≤ val WuPaper.ClassicalFourthData.Bq 4046
    have hp : val WuPaper.ClassicalFourthData.Bq 4046 = (232070633374633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4046 = 232070633374633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4046 = (6023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4047) ≤ val WuPaper.ClassicalFourthData.Bq 4047
    have hp : val WuPaper.ClassicalFourthData.Bq 4047 = (232092633865396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4047 = 232092633865396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4047 = (12047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_252
