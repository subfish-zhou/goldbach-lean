import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints017
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_017 (j : Fin 16) (hj : 16*17+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*17+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*17+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 272) ≤ val WuPaper.ClassicalFourthData.Bq 272
    have hp : val WuPaper.ClassicalFourthData.Bq 272 = (31812253645070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 272 = 31812253645070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 272 = (517:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 273) ≤ val WuPaper.ClassicalFourthData.Bq 273
    have hp : val WuPaper.ClassicalFourthData.Bq 273 = (31921574056327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 273 = 31921574056327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 273 = (8273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 274) ≤ val WuPaper.ClassicalFourthData.Bq 274
    have hp : val WuPaper.ClassicalFourthData.Bq 274 = (32030841564934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 274 = 32030841564934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 274 = (4137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 275) ≤ val WuPaper.ClassicalFourthData.Bq 275
    have hp : val WuPaper.ClassicalFourthData.Bq 275 = (32140056202458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 275 = 32140056202458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 275 = (331:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 276) ≤ val WuPaper.ClassicalFourthData.Bq 276
    have hp : val WuPaper.ClassicalFourthData.Bq 276 = (32249218000439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 276 = 32249218000439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 276 = (2069:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 277) ≤ val WuPaper.ClassicalFourthData.Bq 277
    have hp : val WuPaper.ClassicalFourthData.Bq 277 = (32358326990398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 277 = 32358326990398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 277 = (8277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 278) ≤ val WuPaper.ClassicalFourthData.Bq 278
    have hp : val WuPaper.ClassicalFourthData.Bq 278 = (32467383203829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 278 = 32467383203829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 278 = (4139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 279) ≤ val WuPaper.ClassicalFourthData.Bq 279
    have hp : val WuPaper.ClassicalFourthData.Bq 279 = (32576386672202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 279 = 32576386672202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 279 = (8279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 280) ≤ val WuPaper.ClassicalFourthData.Bq 280
    have hp : val WuPaper.ClassicalFourthData.Bq 280 = (32685337426964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 280 = 32685337426964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 280 = (207:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 281) ≤ val WuPaper.ClassicalFourthData.Bq 281
    have hp : val WuPaper.ClassicalFourthData.Bq 281 = (32794235499538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 281 = 32794235499538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 281 = (8281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 282) ≤ val WuPaper.ClassicalFourthData.Bq 282
    have hp : val WuPaper.ClassicalFourthData.Bq 282 = (32903080921324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 282 = 32903080921324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 282 = (4141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 283) ≤ val WuPaper.ClassicalFourthData.Bq 283
    have hp : val WuPaper.ClassicalFourthData.Bq 283 = (33011873723696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 283 = 33011873723696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 283 = (8283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 284) ≤ val WuPaper.ClassicalFourthData.Bq 284
    have hp : val WuPaper.ClassicalFourthData.Bq 284 = (33120613938007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 284 = 33120613938007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 284 = (2071:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 285) ≤ val WuPaper.ClassicalFourthData.Bq 285
    have hp : val WuPaper.ClassicalFourthData.Bq 285 = (33229301595584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 285 = 33229301595584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 285 = (1657:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 286) ≤ val WuPaper.ClassicalFourthData.Bq 286
    have hp : val WuPaper.ClassicalFourthData.Bq 286 = (33337936727731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 286 = 33337936727731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 286 = (4143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 287) ≤ val WuPaper.ClassicalFourthData.Bq 287
    have hp : val WuPaper.ClassicalFourthData.Bq 287 = (33446519365730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 287 = 33446519365730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 287 = (8287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_017
