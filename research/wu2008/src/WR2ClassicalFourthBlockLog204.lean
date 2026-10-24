import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints204
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_204 (j : Fin 16) (hj : 16*204+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*204+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*204+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3264) ≤ val WuPaper.ClassicalFourthData.Bq 3264
    have hp : val WuPaper.ClassicalFourthData.Bq 3264 = (211873679040875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3264 = 211873679040875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3264 = (352:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3265) ≤ val WuPaper.ClassicalFourthData.Bq 3265
    have hp : val WuPaper.ClassicalFourthData.Bq 3265 = (211903749987521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3265 = 211903749987521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3265 = (2253:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3266) ≤ val WuPaper.ClassicalFourthData.Bq 3266
    have hp : val WuPaper.ClassicalFourthData.Bq 3266 = (211933808868852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3266 = 211933808868852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3266 = (5633:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3267) ≤ val WuPaper.ClassicalFourthData.Bq 3267
    have hp : val WuPaper.ClassicalFourthData.Bq 3267 = (211963855689930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3267 = 211963855689930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3267 = (11267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3268) ≤ val WuPaper.ClassicalFourthData.Bq 3268
    have hp : val WuPaper.ClassicalFourthData.Bq 3268 = (211993890455817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3268 = 211993890455817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3268 = (2817:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3269) ≤ val WuPaper.ClassicalFourthData.Bq 3269
    have hp : val WuPaper.ClassicalFourthData.Bq 3269 = (212023913171571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3269 = 212023913171571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3269 = (11269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3270) ≤ val WuPaper.ClassicalFourthData.Bq 3270
    have hp : val WuPaper.ClassicalFourthData.Bq 3270 = (212053923842250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3270 = 212053923842250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3270 = (1127:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3271) ≤ val WuPaper.ClassicalFourthData.Bq 3271
    have hp : val WuPaper.ClassicalFourthData.Bq 3271 = (212083922472906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3271 = 212083922472906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3271 = (11271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3271
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3272) ≤ val WuPaper.ClassicalFourthData.Bq 3272
    have hp : val WuPaper.ClassicalFourthData.Bq 3272 = (212113909068591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3272 = 212113909068591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3272 = (1409:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3273) ≤ val WuPaper.ClassicalFourthData.Bq 3273
    have hp : val WuPaper.ClassicalFourthData.Bq 3273 = (212143883634353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3273 = 212143883634353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3273 = (11273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3274) ≤ val WuPaper.ClassicalFourthData.Bq 3274
    have hp : val WuPaper.ClassicalFourthData.Bq 3274 = (212173846175238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3274 = 212173846175238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3274 = (5637:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3275) ≤ val WuPaper.ClassicalFourthData.Bq 3275
    have hp : val WuPaper.ClassicalFourthData.Bq 3275 = (212203796696290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3275 = 212203796696290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3275 = (451:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3276) ≤ val WuPaper.ClassicalFourthData.Bq 3276
    have hp : val WuPaper.ClassicalFourthData.Bq 3276 = (212233735202549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3276 = 212233735202549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3276 = (2819:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3277) ≤ val WuPaper.ClassicalFourthData.Bq 3277
    have hp : val WuPaper.ClassicalFourthData.Bq 3277 = (212263661699055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3277 = 212263661699055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3277 = (11277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3278) ≤ val WuPaper.ClassicalFourthData.Bq 3278
    have hp : val WuPaper.ClassicalFourthData.Bq 3278 = (212293576190842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3278 = 212293576190842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3278 = (5639:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3279) ≤ val WuPaper.ClassicalFourthData.Bq 3279
    have hp : val WuPaper.ClassicalFourthData.Bq 3279 = (212323478682944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3279 = 212323478682944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3279 = (11279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_204
