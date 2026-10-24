import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints452
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_452 (j : Fin 16) (hj : 16*452+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*452+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*452+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7232) ≤ val WuPaper.ClassicalFourthData.Bq 7232
    have hp : val WuPaper.ClassicalFourthData.Bq 7232 = (271132480610300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7232 = 271132480610300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7232 = (476:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7233) ≤ val WuPaper.ClassicalFourthData.Bq 7233
    have hp : val WuPaper.ClassicalFourthData.Bq 7233 = (271138059092759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7233 = 271138059092759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7233 = (15233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7234) ≤ val WuPaper.ClassicalFourthData.Bq 7234
    have hp : val WuPaper.ClassicalFourthData.Bq 7234 = (271143634761929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7234 = 271143634761929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7234 = (7617:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7235) ≤ val WuPaper.ClassicalFourthData.Bq 7235
    have hp : val WuPaper.ClassicalFourthData.Bq 7235 = (271149207618736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7235 = 271149207618736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7235 = (3047:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7236) ≤ val WuPaper.ClassicalFourthData.Bq 7236
    have hp : val WuPaper.ClassicalFourthData.Bq 7236 = (271154777664103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7236 = 271154777664103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7236 = (3809:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7237) ≤ val WuPaper.ClassicalFourthData.Bq 7237
    have hp : val WuPaper.ClassicalFourthData.Bq 7237 = (271160344898953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7237 = 271160344898953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7237 = (15237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7238) ≤ val WuPaper.ClassicalFourthData.Bq 7238
    have hp : val WuPaper.ClassicalFourthData.Bq 7238 = (271165909324210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7238 = 271165909324210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7238 = (7619:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7239) ≤ val WuPaper.ClassicalFourthData.Bq 7239
    have hp : val WuPaper.ClassicalFourthData.Bq 7239 = (271171470940797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7239 = 271171470940797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7239 = (15239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7239
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7240) ≤ val WuPaper.ClassicalFourthData.Bq 7240
    have hp : val WuPaper.ClassicalFourthData.Bq 7240 = (271177029749638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7240 = 271177029749638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7240 = (381:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7241) ≤ val WuPaper.ClassicalFourthData.Bq 7241
    have hp : val WuPaper.ClassicalFourthData.Bq 7241 = (271182585751653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7241 = 271182585751653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7241 = (15241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7242) ≤ val WuPaper.ClassicalFourthData.Bq 7242
    have hp : val WuPaper.ClassicalFourthData.Bq 7242 = (271188138947765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7242 = 271188138947765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7242 = (7621:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7243) ≤ val WuPaper.ClassicalFourthData.Bq 7243
    have hp : val WuPaper.ClassicalFourthData.Bq 7243 = (271193689338897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7243 = 271193689338897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7243 = (15243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7244) ≤ val WuPaper.ClassicalFourthData.Bq 7244
    have hp : val WuPaper.ClassicalFourthData.Bq 7244 = (271199236925968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7244 = 271199236925968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7244 = (3811:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7245) ≤ val WuPaper.ClassicalFourthData.Bq 7245
    have hp : val WuPaper.ClassicalFourthData.Bq 7245 = (271204781709901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7245 = 271204781709901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7245 = (3049:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7246) ≤ val WuPaper.ClassicalFourthData.Bq 7246
    have hp : val WuPaper.ClassicalFourthData.Bq 7246 = (271210323691615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7246 = 271210323691615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7246 = (7623:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7247) ≤ val WuPaper.ClassicalFourthData.Bq 7247
    have hp : val WuPaper.ClassicalFourthData.Bq 7247 = (271215862872032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7247 = 271215862872032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7247 = (15247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_452
