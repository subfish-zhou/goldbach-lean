import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints196
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_196 (j : Fin 16) (hj : 16*196+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*196+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*196+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3136) ≤ val WuPaper.ClassicalFourthData.Bq 3136
    have hp : val WuPaper.ClassicalFourthData.Bq 3136 = (207923144453240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3136 = 207923144453240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3136 = (348:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3137) ≤ val WuPaper.ClassicalFourthData.Bq 3137
    have hp : val WuPaper.ClassicalFourthData.Bq 3137 = (207954802503023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3137 = 207954802503023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3137 = (11137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3138) ≤ val WuPaper.ClassicalFourthData.Bq 3138
    have hp : val WuPaper.ClassicalFourthData.Bq 3138 = (207986447817590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3138 = 207986447817590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3138 = (5569:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3139) ≤ val WuPaper.ClassicalFourthData.Bq 3139
    have hp : val WuPaper.ClassicalFourthData.Bq 3139 = (208018080402346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3139 = 208018080402346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3139 = (11139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3140) ≤ val WuPaper.ClassicalFourthData.Bq 3140
    have hp : val WuPaper.ClassicalFourthData.Bq 3140 = (208049700262694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3140 = 208049700262694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3140 = (557:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3141) ≤ val WuPaper.ClassicalFourthData.Bq 3141
    have hp : val WuPaper.ClassicalFourthData.Bq 3141 = (208081307404033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3141 = 208081307404033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3141 = (11141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3142) ≤ val WuPaper.ClassicalFourthData.Bq 3142
    have hp : val WuPaper.ClassicalFourthData.Bq 3142 = (208112901831760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3142 = 208112901831760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3142 = (5571:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3143) ≤ val WuPaper.ClassicalFourthData.Bq 3143
    have hp : val WuPaper.ClassicalFourthData.Bq 3143 = (208144483551268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3143 = 208144483551268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3143 = (11143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3143
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3144) ≤ val WuPaper.ClassicalFourthData.Bq 3144
    have hp : val WuPaper.ClassicalFourthData.Bq 3144 = (208176052567950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3144 = 208176052567950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3144 = (1393:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3145) ≤ val WuPaper.ClassicalFourthData.Bq 3145
    have hp : val WuPaper.ClassicalFourthData.Bq 3145 = (208207608887193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3145 = 208207608887193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3145 = (2229:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3146) ≤ val WuPaper.ClassicalFourthData.Bq 3146
    have hp : val WuPaper.ClassicalFourthData.Bq 3146 = (208239152514383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3146 = 208239152514383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3146 = (5573:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3147) ≤ val WuPaper.ClassicalFourthData.Bq 3147
    have hp : val WuPaper.ClassicalFourthData.Bq 3147 = (208270683454904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3147 = 208270683454904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3147 = (11147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3148) ≤ val WuPaper.ClassicalFourthData.Bq 3148
    have hp : val WuPaper.ClassicalFourthData.Bq 3148 = (208302201714134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3148 = 208302201714134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3148 = (2787:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3149) ≤ val WuPaper.ClassicalFourthData.Bq 3149
    have hp : val WuPaper.ClassicalFourthData.Bq 3149 = (208333707297453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3149 = 208333707297453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3149 = (11149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3150) ≤ val WuPaper.ClassicalFourthData.Bq 3150
    have hp : val WuPaper.ClassicalFourthData.Bq 3150 = (208365200210234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3150 = 208365200210234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3150 = (223:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3151) ≤ val WuPaper.ClassicalFourthData.Bq 3151
    have hp : val WuPaper.ClassicalFourthData.Bq 3151 = (208396680457849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3151 = 208396680457849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3151 = (11151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_196
