import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints135
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_135 (j : Fin 16) (hj : 16*135+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*135+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*135+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2160) ≤ val WuPaper.ClassicalFourthData.Bq 2160
    have hp : val WuPaper.ClassicalFourthData.Bq 2160 = (169993077332889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2160 = 169993077332889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2160 = (127:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2161) ≤ val WuPaper.ClassicalFourthData.Bq 2161
    have hp : val WuPaper.ClassicalFourthData.Bq 2161 = (170040248366320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2161 = 170040248366320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2161 = (10161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2162) ≤ val WuPaper.ClassicalFourthData.Bq 2162
    have hp : val WuPaper.ClassicalFourthData.Bq 2162 = (170087399745950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2162 = 170087399745950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2162 = (5081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2163) ≤ val WuPaper.ClassicalFourthData.Bq 2163
    have hp : val WuPaper.ClassicalFourthData.Bq 2163 = (170134531480947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2163 = 170134531480947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2163 = (10163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2164) ≤ val WuPaper.ClassicalFourthData.Bq 2164
    have hp : val WuPaper.ClassicalFourthData.Bq 2164 = (170181643580472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2164 = 170181643580472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2164 = (2541:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2165) ≤ val WuPaper.ClassicalFourthData.Bq 2165
    have hp : val WuPaper.ClassicalFourthData.Bq 2165 = (170228736053682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2165 = 170228736053682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2165 = (2033:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2166) ≤ val WuPaper.ClassicalFourthData.Bq 2166
    have hp : val WuPaper.ClassicalFourthData.Bq 2166 = (170275808909726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2166 = 170275808909726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2166 = (5083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2167) ≤ val WuPaper.ClassicalFourthData.Bq 2167
    have hp : val WuPaper.ClassicalFourthData.Bq 2167 = (170322862157752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2167 = 170322862157752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2167 = (10167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2168) ≤ val WuPaper.ClassicalFourthData.Bq 2168
    have hp : val WuPaper.ClassicalFourthData.Bq 2168 = (170369895806900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2168 = 170369895806900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2168 = (1271:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2169) ≤ val WuPaper.ClassicalFourthData.Bq 2169
    have hp : val WuPaper.ClassicalFourthData.Bq 2169 = (170416909866304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2169 = 170416909866304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2169 = (10169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2170) ≤ val WuPaper.ClassicalFourthData.Bq 2170
    have hp : val WuPaper.ClassicalFourthData.Bq 2170 = (170463904345096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2170 = 170463904345096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2170 = (1017:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2171) ≤ val WuPaper.ClassicalFourthData.Bq 2171
    have hp : val WuPaper.ClassicalFourthData.Bq 2171 = (170510879252400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2171 = 170510879252400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2171 = (10171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2172) ≤ val WuPaper.ClassicalFourthData.Bq 2172
    have hp : val WuPaper.ClassicalFourthData.Bq 2172 = (170557834597336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2172 = 170557834597336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2172 = (2543:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2173) ≤ val WuPaper.ClassicalFourthData.Bq 2173
    have hp : val WuPaper.ClassicalFourthData.Bq 2173 = (170604770389018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2173 = 170604770389018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2173 = (10173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2174) ≤ val WuPaper.ClassicalFourthData.Bq 2174
    have hp : val WuPaper.ClassicalFourthData.Bq 2174 = (170651686636555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2174 = 170651686636555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2174 = (5087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2175) ≤ val WuPaper.ClassicalFourthData.Bq 2175
    have hp : val WuPaper.ClassicalFourthData.Bq 2175 = (170698583349052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2175 = 170698583349052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2175 = (407:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_135
