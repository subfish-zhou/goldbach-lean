import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints141
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_141 (j : Fin 16) (hj : 16*141+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*141+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*141+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2256) ≤ val WuPaper.ClassicalFourthData.Bq 2256
    have hp : val WuPaper.ClassicalFourthData.Bq 2256 = (174433167754727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2256 = 174433167754727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2256 = (641:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2257) ≤ val WuPaper.ClassicalFourthData.Bq 2257
    have hp : val WuPaper.ClassicalFourthData.Bq 2257 = (174478493086219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2257 = 174478493086219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2257 = (10257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2258) ≤ val WuPaper.ClassicalFourthData.Bq 2258
    have hp : val WuPaper.ClassicalFourthData.Bq 2258 = (174523799620511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2258 = 174523799620511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2258 = (5129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2259) ≤ val WuPaper.ClassicalFourthData.Bq 2259
    have hp : val WuPaper.ClassicalFourthData.Bq 2259 = (174569087366283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2259 = 174569087366283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2259 = (10259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2260) ≤ val WuPaper.ClassicalFourthData.Bq 2260
    have hp : val WuPaper.ClassicalFourthData.Bq 2260 = (174614356332210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2260 = 174614356332210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2260 = (513:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2261) ≤ val WuPaper.ClassicalFourthData.Bq 2261
    have hp : val WuPaper.ClassicalFourthData.Bq 2261 = (174659606526960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2261 = 174659606526960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2261 = (10261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2262) ≤ val WuPaper.ClassicalFourthData.Bq 2262
    have hp : val WuPaper.ClassicalFourthData.Bq 2262 = (174704837959199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2262 = 174704837959199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2262 = (5131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2263) ≤ val WuPaper.ClassicalFourthData.Bq 2263
    have hp : val WuPaper.ClassicalFourthData.Bq 2263 = (174750050637586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2263 = 174750050637586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2263 = (10263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2264) ≤ val WuPaper.ClassicalFourthData.Bq 2264
    have hp : val WuPaper.ClassicalFourthData.Bq 2264 = (174795244570777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2264 = 174795244570777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2264 = (1283:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2265) ≤ val WuPaper.ClassicalFourthData.Bq 2265
    have hp : val WuPaper.ClassicalFourthData.Bq 2265 = (174840419767420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2265 = 174840419767420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2265 = (2053:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2266) ≤ val WuPaper.ClassicalFourthData.Bq 2266
    have hp : val WuPaper.ClassicalFourthData.Bq 2266 = (174885576236162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2266 = 174885576236162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2266 = (5133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2267) ≤ val WuPaper.ClassicalFourthData.Bq 2267
    have hp : val WuPaper.ClassicalFourthData.Bq 2267 = (174930713985643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2267 = 174930713985643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2267 = (10267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2268) ≤ val WuPaper.ClassicalFourthData.Bq 2268
    have hp : val WuPaper.ClassicalFourthData.Bq 2268 = (174975833024497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2268 = 174975833024497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2268 = (2567:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2269) ≤ val WuPaper.ClassicalFourthData.Bq 2269
    have hp : val WuPaper.ClassicalFourthData.Bq 2269 = (175020933361356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2269 = 175020933361356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2269 = (10269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2270) ≤ val WuPaper.ClassicalFourthData.Bq 2270
    have hp : val WuPaper.ClassicalFourthData.Bq 2270 = (175066015004845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2270 = 175066015004845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2270 = (1027:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2271) ≤ val WuPaper.ClassicalFourthData.Bq 2271
    have hp : val WuPaper.ClassicalFourthData.Bq 2271 = (175111077963585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2271 = 175111077963585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2271 = (10271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_141
