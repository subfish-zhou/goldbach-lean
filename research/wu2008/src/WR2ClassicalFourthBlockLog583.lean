import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints583
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_583 (j : Fin 16) (hj : 16*583+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*583+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*583+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9328) ≤ val WuPaper.ClassicalFourthData.Bq 9328
    have hp : val WuPaper.ClassicalFourthData.Bq 9328 = (277833038858802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9328 = 277833038858802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9328 = (1083:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9329) ≤ val WuPaper.ClassicalFourthData.Bq 9329
    have hp : val WuPaper.ClassicalFourthData.Bq 9329 = (277834324319644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9329 = 277834324319644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9329 = (17329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9330) ≤ val WuPaper.ClassicalFourthData.Bq 9330
    have hp : val WuPaper.ClassicalFourthData.Bq 9330 = (277835608332965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9330 = 277835608332965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9330 = (1733:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9331) ≤ val WuPaper.ClassicalFourthData.Bq 9331
    have hp : val WuPaper.ClassicalFourthData.Bq 9331 = (277836890899209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9331 = 277836890899209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9331 = (17331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9332) ≤ val WuPaper.ClassicalFourthData.Bq 9332
    have hp : val WuPaper.ClassicalFourthData.Bq 9332 = (277838172018822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9332 = 277838172018822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9332 = (4333:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9333) ≤ val WuPaper.ClassicalFourthData.Bq 9333
    have hp : val WuPaper.ClassicalFourthData.Bq 9333 = (277839451692249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9333 = 277839451692249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9333 = (17333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9334) ≤ val WuPaper.ClassicalFourthData.Bq 9334
    have hp : val WuPaper.ClassicalFourthData.Bq 9334 = (277840729919935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9334 = 277840729919935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9334 = (8667:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9335) ≤ val WuPaper.ClassicalFourthData.Bq 9335
    have hp : val WuPaper.ClassicalFourthData.Bq 9335 = (277842006702326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9335 = 277842006702326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9335 = (3467:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9335
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9336) ≤ val WuPaper.ClassicalFourthData.Bq 9336
    have hp : val WuPaper.ClassicalFourthData.Bq 9336 = (277843282039865:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9336 = 277843282039865 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9336 = (2167:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9337) ≤ val WuPaper.ClassicalFourthData.Bq 9337
    have hp : val WuPaper.ClassicalFourthData.Bq 9337 = (277844555932998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9337 = 277844555932998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9337 = (17337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9338) ≤ val WuPaper.ClassicalFourthData.Bq 9338
    have hp : val WuPaper.ClassicalFourthData.Bq 9338 = (277845828382168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9338 = 277845828382168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9338 = (8669:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9339) ≤ val WuPaper.ClassicalFourthData.Bq 9339
    have hp : val WuPaper.ClassicalFourthData.Bq 9339 = (277847099387820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9339 = 277847099387820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9339 = (17339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9340) ≤ val WuPaper.ClassicalFourthData.Bq 9340
    have hp : val WuPaper.ClassicalFourthData.Bq 9340 = (277848368950399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9340 = 277848368950399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9340 = (867:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9341) ≤ val WuPaper.ClassicalFourthData.Bq 9341
    have hp : val WuPaper.ClassicalFourthData.Bq 9341 = (277849637070348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9341 = 277849637070348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9341 = (17341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9342) ≤ val WuPaper.ClassicalFourthData.Bq 9342
    have hp : val WuPaper.ClassicalFourthData.Bq 9342 = (277850903748112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9342 = 277850903748112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9342 = (8671:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9343) ≤ val WuPaper.ClassicalFourthData.Bq 9343
    have hp : val WuPaper.ClassicalFourthData.Bq 9343 = (277852168984133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9343 = 277852168984133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9343 = (17343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_583
