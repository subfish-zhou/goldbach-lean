import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints329
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_329 (j : Fin 16) (hj : 16*329+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*329+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*329+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5264) ≤ val WuPaper.ClassicalFourthData.Bq 5264
    have hp : val WuPaper.ClassicalFourthData.Bq 5264 = (253269469152820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5264 = 253269469152820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5264 = (829:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5265) ≤ val WuPaper.ClassicalFourthData.Bq 5265
    have hp : val WuPaper.ClassicalFourthData.Bq 5265 = (253282924573671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5265 = 253282924573671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5265 = (2653:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5266) ≤ val WuPaper.ClassicalFourthData.Bq 5266
    have hp : val WuPaper.ClassicalFourthData.Bq 5266 = (253296374453360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5266 = 253296374453360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5266 = (6633:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5267) ≤ val WuPaper.ClassicalFourthData.Bq 5267
    have hp : val WuPaper.ClassicalFourthData.Bq 5267 = (253309818793900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5267 = 253309818793900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5267 = (13267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5268) ≤ val WuPaper.ClassicalFourthData.Bq 5268
    have hp : val WuPaper.ClassicalFourthData.Bq 5268 = (253323257597299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5268 = 253323257597299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5268 = (3317:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5269) ≤ val WuPaper.ClassicalFourthData.Bq 5269
    have hp : val WuPaper.ClassicalFourthData.Bq 5269 = (253336690865569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5269 = 253336690865569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5269 = (13269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5270) ≤ val WuPaper.ClassicalFourthData.Bq 5270
    have hp : val WuPaper.ClassicalFourthData.Bq 5270 = (253350118600716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5270 = 253350118600716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5270 = (1327:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5271) ≤ val WuPaper.ClassicalFourthData.Bq 5271
    have hp : val WuPaper.ClassicalFourthData.Bq 5271 = (253363540804750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5271 = 253363540804750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5271 = (13271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5271
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5272) ≤ val WuPaper.ClassicalFourthData.Bq 5272
    have hp : val WuPaper.ClassicalFourthData.Bq 5272 = (253376957479675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5272 = 253376957479675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5272 = (1659:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5273) ≤ val WuPaper.ClassicalFourthData.Bq 5273
    have hp : val WuPaper.ClassicalFourthData.Bq 5273 = (253390368627500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5273 = 253390368627500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5273 = (13273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5274) ≤ val WuPaper.ClassicalFourthData.Bq 5274
    have hp : val WuPaper.ClassicalFourthData.Bq 5274 = (253403774250228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5274 = 253403774250228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5274 = (6637:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5275) ≤ val WuPaper.ClassicalFourthData.Bq 5275
    have hp : val WuPaper.ClassicalFourthData.Bq 5275 = (253417174349864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5275 = 253417174349864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5275 = (531:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5276) ≤ val WuPaper.ClassicalFourthData.Bq 5276
    have hp : val WuPaper.ClassicalFourthData.Bq 5276 = (253430568928411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5276 = 253430568928411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5276 = (3319:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5277) ≤ val WuPaper.ClassicalFourthData.Bq 5277
    have hp : val WuPaper.ClassicalFourthData.Bq 5277 = (253443957987873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5277 = 253443957987873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5277 = (13277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5278) ≤ val WuPaper.ClassicalFourthData.Bq 5278
    have hp : val WuPaper.ClassicalFourthData.Bq 5278 = (253457341530250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5278 = 253457341530250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5278 = (6639:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5279) ≤ val WuPaper.ClassicalFourthData.Bq 5279
    have hp : val WuPaper.ClassicalFourthData.Bq 5279 = (253470719557543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5279 = 253470719557543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5279 = (13279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_329
