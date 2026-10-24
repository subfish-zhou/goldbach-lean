import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints142
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_142 (j : Fin 16) (hj : 16*142+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*142+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*142+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2272) ≤ val WuPaper.ClassicalFourthData.Bq 2272
    have hp : val WuPaper.ClassicalFourthData.Bq 2272 = (175156122246191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2272 = 175156122246191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2272 = (321:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2273) ≤ val WuPaper.ClassicalFourthData.Bq 2273
    have hp : val WuPaper.ClassicalFourthData.Bq 2273 = (175201147861274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2273 = 175201147861274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2273 = (10273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2274) ≤ val WuPaper.ClassicalFourthData.Bq 2274
    have hp : val WuPaper.ClassicalFourthData.Bq 2274 = (175246154817441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2274 = 175246154817441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2274 = (5137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2275) ≤ val WuPaper.ClassicalFourthData.Bq 2275
    have hp : val WuPaper.ClassicalFourthData.Bq 2275 = (175291143123293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2275 = 175291143123293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2275 = (411:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2276) ≤ val WuPaper.ClassicalFourthData.Bq 2276
    have hp : val WuPaper.ClassicalFourthData.Bq 2276 = (175336112787426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2276 = 175336112787426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2276 = (2569:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2277) ≤ val WuPaper.ClassicalFourthData.Bq 2277
    have hp : val WuPaper.ClassicalFourthData.Bq 2277 = (175381063818432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2277 = 175381063818432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2277 = (10277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2278) ≤ val WuPaper.ClassicalFourthData.Bq 2278
    have hp : val WuPaper.ClassicalFourthData.Bq 2278 = (175425996224897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2278 = 175425996224897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2278 = (5139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2279) ≤ val WuPaper.ClassicalFourthData.Bq 2279
    have hp : val WuPaper.ClassicalFourthData.Bq 2279 = (175470910015403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2279 = 175470910015403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2279 = (10279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2280) ≤ val WuPaper.ClassicalFourthData.Bq 2280
    have hp : val WuPaper.ClassicalFourthData.Bq 2280 = (175515805198528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2280 = 175515805198528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2280 = (257:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2281) ≤ val WuPaper.ClassicalFourthData.Bq 2281
    have hp : val WuPaper.ClassicalFourthData.Bq 2281 = (175560681782844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2281 = 175560681782844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2281 = (10281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2282) ≤ val WuPaper.ClassicalFourthData.Bq 2282
    have hp : val WuPaper.ClassicalFourthData.Bq 2282 = (175605539776917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2282 = 175605539776917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2282 = (5141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2283) ≤ val WuPaper.ClassicalFourthData.Bq 2283
    have hp : val WuPaper.ClassicalFourthData.Bq 2283 = (175650379189311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2283 = 175650379189311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2283 = (10283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2284) ≤ val WuPaper.ClassicalFourthData.Bq 2284
    have hp : val WuPaper.ClassicalFourthData.Bq 2284 = (175695200028582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2284 = 175695200028582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2284 = (2571:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2285) ≤ val WuPaper.ClassicalFourthData.Bq 2285
    have hp : val WuPaper.ClassicalFourthData.Bq 2285 = (175740002303285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2285 = 175740002303285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2285 = (2057:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2286) ≤ val WuPaper.ClassicalFourthData.Bq 2286
    have hp : val WuPaper.ClassicalFourthData.Bq 2286 = (175784786021966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2286 = 175784786021966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2286 = (5143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2287) ≤ val WuPaper.ClassicalFourthData.Bq 2287
    have hp : val WuPaper.ClassicalFourthData.Bq 2287 = (175829551193170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2287 = 175829551193170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2287 = (10287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_142
