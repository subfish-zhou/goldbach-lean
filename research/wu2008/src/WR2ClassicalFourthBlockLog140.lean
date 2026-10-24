import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints140
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_140 (j : Fin 16) (hj : 16*140+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*140+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*140+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2240) ≤ val WuPaper.ClassicalFourthData.Bq 2240
    have hp : val WuPaper.ClassicalFourthData.Bq 2240 = (173705398930253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2240 = 173705398930253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2240 = (64:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2241) ≤ val WuPaper.ClassicalFourthData.Bq 2241
    have hp : val WuPaper.ClassicalFourthData.Bq 2241 = (173751026201354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2241 = 173751026201354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2241 = (10241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2242) ≤ val WuPaper.ClassicalFourthData.Bq 2242
    have hp : val WuPaper.ClassicalFourthData.Bq 2242 = (173796634535715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2242 = 173796634535715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2242 = (5121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2243) ≤ val WuPaper.ClassicalFourthData.Bq 2243
    have hp : val WuPaper.ClassicalFourthData.Bq 2243 = (173842223942094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2243 = 173842223942094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2243 = (10243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2244) ≤ val WuPaper.ClassicalFourthData.Bq 2244
    have hp : val WuPaper.ClassicalFourthData.Bq 2244 = (173887794429245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2244 = 173887794429245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2244 = (2561:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2245) ≤ val WuPaper.ClassicalFourthData.Bq 2245
    have hp : val WuPaper.ClassicalFourthData.Bq 2245 = (173933346005916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2245 = 173933346005916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2245 = (2049:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2246) ≤ val WuPaper.ClassicalFourthData.Bq 2246
    have hp : val WuPaper.ClassicalFourthData.Bq 2246 = (173978878680850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2246 = 173978878680850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2246 = (5123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2247) ≤ val WuPaper.ClassicalFourthData.Bq 2247
    have hp : val WuPaper.ClassicalFourthData.Bq 2247 = (174024392462787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2247 = 174024392462787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2247 = (10247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2248) ≤ val WuPaper.ClassicalFourthData.Bq 2248
    have hp : val WuPaper.ClassicalFourthData.Bq 2248 = (174069887360459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2248 = 174069887360459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2248 = (1281:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2249) ≤ val WuPaper.ClassicalFourthData.Bq 2249
    have hp : val WuPaper.ClassicalFourthData.Bq 2249 = (174115363382595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2249 = 174115363382595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2249 = (10249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2250) ≤ val WuPaper.ClassicalFourthData.Bq 2250
    have hp : val WuPaper.ClassicalFourthData.Bq 2250 = (174160820537920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2250 = 174160820537920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2250 = (41:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2251) ≤ val WuPaper.ClassicalFourthData.Bq 2251
    have hp : val WuPaper.ClassicalFourthData.Bq 2251 = (174206258835152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2251 = 174206258835152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2251 = (10251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2252) ≤ val WuPaper.ClassicalFourthData.Bq 2252
    have hp : val WuPaper.ClassicalFourthData.Bq 2252 = (174251678283005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2252 = 174251678283005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2252 = (2563:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2253) ≤ val WuPaper.ClassicalFourthData.Bq 2253
    have hp : val WuPaper.ClassicalFourthData.Bq 2253 = (174297078890187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2253 = 174297078890187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2253 = (10253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2254) ≤ val WuPaper.ClassicalFourthData.Bq 2254
    have hp : val WuPaper.ClassicalFourthData.Bq 2254 = (174342460665403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2254 = 174342460665403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2254 = (5127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2255) ≤ val WuPaper.ClassicalFourthData.Bq 2255
    have hp : val WuPaper.ClassicalFourthData.Bq 2255 = (174387823617352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2255 = 174387823617352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2255 = (2051:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_140
