import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints018
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_018 (j : Fin 16) (hj : 16*18+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*18+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*18+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 288) ≤ val WuPaper.ClassicalFourthData.Bq 288
    have hp : val WuPaper.ClassicalFourthData.Bq 288 = (33555049540836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 288 = 33555049540836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 288 = (259:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 289) ≤ val WuPaper.ClassicalFourthData.Bq 289
    have hp : val WuPaper.ClassicalFourthData.Bq 289 = (33663527284282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 289 = 33663527284282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 289 = (8289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 290) ≤ val WuPaper.ClassicalFourthData.Bq 290
    have hp : val WuPaper.ClassicalFourthData.Bq 290 = (33771952627279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 290 = 33771952627279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 290 = (829:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 291) ≤ val WuPaper.ClassicalFourthData.Bq 291
    have hp : val WuPaper.ClassicalFourthData.Bq 291 = (33880325601012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 291 = 33880325601012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 291 = (8291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 292) ≤ val WuPaper.ClassicalFourthData.Bq 292
    have hp : val WuPaper.ClassicalFourthData.Bq 292 = (33988646236644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 292 = 33988646236644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 292 = (2073:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 293) ≤ val WuPaper.ClassicalFourthData.Bq 293
    have hp : val WuPaper.ClassicalFourthData.Bq 293 = (34096914565312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 293 = 34096914565312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 293 = (8293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 294) ≤ val WuPaper.ClassicalFourthData.Bq 294
    have hp : val WuPaper.ClassicalFourthData.Bq 294 = (34205130618133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 294 = 34205130618133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 294 = (4147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 295) ≤ val WuPaper.ClassicalFourthData.Bq 295
    have hp : val WuPaper.ClassicalFourthData.Bq 295 = (34313294426198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 295 = 34313294426198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 295 = (1659:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 296) ≤ val WuPaper.ClassicalFourthData.Bq 296
    have hp : val WuPaper.ClassicalFourthData.Bq 296 = (34421406020576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 296 = 34421406020576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 296 = (1037:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 297) ≤ val WuPaper.ClassicalFourthData.Bq 297
    have hp : val WuPaper.ClassicalFourthData.Bq 297 = (34529465432310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 297 = 34529465432310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 297 = (8297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 298) ≤ val WuPaper.ClassicalFourthData.Bq 298
    have hp : val WuPaper.ClassicalFourthData.Bq 298 = (34637472692422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 298 = 34637472692422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 298 = (4149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 299) ≤ val WuPaper.ClassicalFourthData.Bq 299
    have hp : val WuPaper.ClassicalFourthData.Bq 299 = (34745427831910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 299 = 34745427831910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 299 = (8299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 300) ≤ val WuPaper.ClassicalFourthData.Bq 300
    have hp : val WuPaper.ClassicalFourthData.Bq 300 = (34853330881748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 300 = 34853330881748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 300 = (83:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 301) ≤ val WuPaper.ClassicalFourthData.Bq 301
    have hp : val WuPaper.ClassicalFourthData.Bq 301 = (34961181872887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 301 = 34961181872887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 301 = (8301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 302) ≤ val WuPaper.ClassicalFourthData.Bq 302
    have hp : val WuPaper.ClassicalFourthData.Bq 302 = (35068980836256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 302 = 35068980836256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 302 = (4151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 303) ≤ val WuPaper.ClassicalFourthData.Bq 303
    have hp : val WuPaper.ClassicalFourthData.Bq 303 = (35176727802757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 303 = 35176727802757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 303 = (8303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_018
