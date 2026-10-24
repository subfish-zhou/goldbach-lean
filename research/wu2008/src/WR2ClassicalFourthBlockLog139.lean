import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints139
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_139 (j : Fin 16) (hj : 16*139+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*139+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*139+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2224) ≤ val WuPaper.ClassicalFourthData.Bq 2224
    have hp : val WuPaper.ClassicalFourthData.Bq 2224 = (172972780029813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2224 = 172972780029813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2224 = (639:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2225) ≤ val WuPaper.ClassicalFourthData.Bq 2225
    have hp : val WuPaper.ClassicalFourthData.Bq 2225 = (173018711483964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2225 = 173018711483964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2225 = (409:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2226) ≤ val WuPaper.ClassicalFourthData.Bq 2226
    have hp : val WuPaper.ClassicalFourthData.Bq 2226 = (173064623860562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2226 = 173064623860562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2226 = (5113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2227) ≤ val WuPaper.ClassicalFourthData.Bq 2227
    have hp : val WuPaper.ClassicalFourthData.Bq 2227 = (173110517168446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2227 = 173110517168446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2227 = (10227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2228) ≤ val WuPaper.ClassicalFourthData.Bq 2228
    have hp : val WuPaper.ClassicalFourthData.Bq 2228 = (173156391416450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2228 = 173156391416450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2228 = (2557:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2229) ≤ val WuPaper.ClassicalFourthData.Bq 2229
    have hp : val WuPaper.ClassicalFourthData.Bq 2229 = (173202246613401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2229 = 173202246613401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2229 = (10229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2230) ≤ val WuPaper.ClassicalFourthData.Bq 2230
    have hp : val WuPaper.ClassicalFourthData.Bq 2230 = (173248082768122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2230 = 173248082768122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2230 = (1023:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2231) ≤ val WuPaper.ClassicalFourthData.Bq 2231
    have hp : val WuPaper.ClassicalFourthData.Bq 2231 = (173293899889432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2231 = 173293899889432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2231 = (10231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2232) ≤ val WuPaper.ClassicalFourthData.Bq 2232
    have hp : val WuPaper.ClassicalFourthData.Bq 2232 = (173339697986145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2232 = 173339697986145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2232 = (1279:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2233) ≤ val WuPaper.ClassicalFourthData.Bq 2233
    have hp : val WuPaper.ClassicalFourthData.Bq 2233 = (173385477067067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2233 = 173385477067067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2233 = (10233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2234) ≤ val WuPaper.ClassicalFourthData.Bq 2234
    have hp : val WuPaper.ClassicalFourthData.Bq 2234 = (173431237141003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2234 = 173431237141003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2234 = (5117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2235) ≤ val WuPaper.ClassicalFourthData.Bq 2235
    have hp : val WuPaper.ClassicalFourthData.Bq 2235 = (173476978216751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2235 = 173476978216751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2235 = (2047:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2236) ≤ val WuPaper.ClassicalFourthData.Bq 2236
    have hp : val WuPaper.ClassicalFourthData.Bq 2236 = (173522700303103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2236 = 173522700303103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2236 = (2559:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2237) ≤ val WuPaper.ClassicalFourthData.Bq 2237
    have hp : val WuPaper.ClassicalFourthData.Bq 2237 = (173568403408849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2237 = 173568403408849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2237 = (10237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2238) ≤ val WuPaper.ClassicalFourthData.Bq 2238
    have hp : val WuPaper.ClassicalFourthData.Bq 2238 = (173614087542771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2238 = 173614087542771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2238 = (5119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2239) ≤ val WuPaper.ClassicalFourthData.Bq 2239
    have hp : val WuPaper.ClassicalFourthData.Bq 2239 = (173659752713648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2239 = 173659752713648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2239 = (10239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_139
