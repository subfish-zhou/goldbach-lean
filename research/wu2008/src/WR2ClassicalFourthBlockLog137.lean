import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints137
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_137 (j : Fin 16) (hj : 16*137+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*137+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*137+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2192) ≤ val WuPaper.ClassicalFourthData.Bq 2192
    have hp : val WuPaper.ClassicalFourthData.Bq 2192 = (171492847396992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2192 = 171492847396992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2192 = (637:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2193) ≤ val WuPaper.ClassicalFourthData.Bq 2193
    have hp : val WuPaper.ClassicalFourthData.Bq 2193 = (171539394029642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2193 = 171539394029642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2193 = (10193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2194) ≤ val WuPaper.ClassicalFourthData.Bq 2194
    have hp : val WuPaper.ClassicalFourthData.Bq 2194 = (171585921299243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2194 = 171585921299243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2194 = (5097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2195) ≤ val WuPaper.ClassicalFourthData.Bq 2195
    have hp : val WuPaper.ClassicalFourthData.Bq 2195 = (171632429214798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2195 = 171632429214798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2195 = (2039:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2196) ≤ val WuPaper.ClassicalFourthData.Bq 2196
    have hp : val WuPaper.ClassicalFourthData.Bq 2196 = (171678917785301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2196 = 171678917785301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2196 = (2549:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2197) ≤ val WuPaper.ClassicalFourthData.Bq 2197
    have hp : val WuPaper.ClassicalFourthData.Bq 2197 = (171725387019743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2197 = 171725387019743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2197 = (10197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2198) ≤ val WuPaper.ClassicalFourthData.Bq 2198
    have hp : val WuPaper.ClassicalFourthData.Bq 2198 = (171771836927110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2198 = 171771836927110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2198 = (5099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2199) ≤ val WuPaper.ClassicalFourthData.Bq 2199
    have hp : val WuPaper.ClassicalFourthData.Bq 2199 = (171818267516381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2199 = 171818267516381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2199 = (10199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2200) ≤ val WuPaper.ClassicalFourthData.Bq 2200
    have hp : val WuPaper.ClassicalFourthData.Bq 2200 = (171864678796532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2200 = 171864678796532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2200 = (51:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2201) ≤ val WuPaper.ClassicalFourthData.Bq 2201
    have hp : val WuPaper.ClassicalFourthData.Bq 2201 = (171911070776532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2201 = 171911070776532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2201 = (10201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2202) ≤ val WuPaper.ClassicalFourthData.Bq 2202
    have hp : val WuPaper.ClassicalFourthData.Bq 2202 = (171957443465347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2202 = 171957443465347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2202 = (5101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2203) ≤ val WuPaper.ClassicalFourthData.Bq 2203
    have hp : val WuPaper.ClassicalFourthData.Bq 2203 = (172003796871936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2203 = 172003796871936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2203 = (10203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2204) ≤ val WuPaper.ClassicalFourthData.Bq 2204
    have hp : val WuPaper.ClassicalFourthData.Bq 2204 = (172050131005254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2204 = 172050131005254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2204 = (2551:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2205) ≤ val WuPaper.ClassicalFourthData.Bq 2205
    have hp : val WuPaper.ClassicalFourthData.Bq 2205 = (172096445874250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2205 = 172096445874250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2205 = (2041:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2206) ≤ val WuPaper.ClassicalFourthData.Bq 2206
    have hp : val WuPaper.ClassicalFourthData.Bq 2206 = (172142741487870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2206 = 172142741487870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2206 = (5103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2207) ≤ val WuPaper.ClassicalFourthData.Bq 2207
    have hp : val WuPaper.ClassicalFourthData.Bq 2207 = (172189017855051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2207 = 172189017855051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2207 = (10207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_137
