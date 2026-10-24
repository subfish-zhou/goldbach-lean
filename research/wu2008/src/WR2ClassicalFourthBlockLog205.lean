import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints205
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_205 (j : Fin 16) (hj : 16*205+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*205+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*205+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3280) ≤ val WuPaper.ClassicalFourthData.Bq 3280
    have hp : val WuPaper.ClassicalFourthData.Bq 3280 = (212353369180392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3280 = 212353369180392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3280 = (141:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3281) ≤ val WuPaper.ClassicalFourthData.Bq 3281
    have hp : val WuPaper.ClassicalFourthData.Bq 3281 = (212383247688214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3281 = 212383247688214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3281 = (11281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3282) ≤ val WuPaper.ClassicalFourthData.Bq 3282
    have hp : val WuPaper.ClassicalFourthData.Bq 3282 = (212413114211435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3282 = 212413114211435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3282 = (5641:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3283) ≤ val WuPaper.ClassicalFourthData.Bq 3283
    have hp : val WuPaper.ClassicalFourthData.Bq 3283 = (212442968755079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3283 = 212442968755079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3283 = (11283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3284) ≤ val WuPaper.ClassicalFourthData.Bq 3284
    have hp : val WuPaper.ClassicalFourthData.Bq 3284 = (212472811324166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3284 = 212472811324166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3284 = (2821:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3285) ≤ val WuPaper.ClassicalFourthData.Bq 3285
    have hp : val WuPaper.ClassicalFourthData.Bq 3285 = (212502641923714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3285 = 212502641923714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3285 = (2257:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3286) ≤ val WuPaper.ClassicalFourthData.Bq 3286
    have hp : val WuPaper.ClassicalFourthData.Bq 3286 = (212532460558739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3286 = 212532460558739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3286 = (5643:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3287) ≤ val WuPaper.ClassicalFourthData.Bq 3287
    have hp : val WuPaper.ClassicalFourthData.Bq 3287 = (212562267234254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3287 = 212562267234254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3287 = (11287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3287
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3288) ≤ val WuPaper.ClassicalFourthData.Bq 3288
    have hp : val WuPaper.ClassicalFourthData.Bq 3288 = (212592061955269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3288 = 212592061955269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3288 = (1411:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3289) ≤ val WuPaper.ClassicalFourthData.Bq 3289
    have hp : val WuPaper.ClassicalFourthData.Bq 3289 = (212621844726791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3289 = 212621844726791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3289 = (11289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3290) ≤ val WuPaper.ClassicalFourthData.Bq 3290
    have hp : val WuPaper.ClassicalFourthData.Bq 3290 = (212651615553827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3290 = 212651615553827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3290 = (1129:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3291) ≤ val WuPaper.ClassicalFourthData.Bq 3291
    have hp : val WuPaper.ClassicalFourthData.Bq 3291 = (212681374441380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3291 = 212681374441380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3291 = (11291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3292) ≤ val WuPaper.ClassicalFourthData.Bq 3292
    have hp : val WuPaper.ClassicalFourthData.Bq 3292 = (212711121394448:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3292 = 212711121394448 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3292 = (2823:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3293) ≤ val WuPaper.ClassicalFourthData.Bq 3293
    have hp : val WuPaper.ClassicalFourthData.Bq 3293 = (212740856418031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3293 = 212740856418031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3293 = (11293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3294) ≤ val WuPaper.ClassicalFourthData.Bq 3294
    have hp : val WuPaper.ClassicalFourthData.Bq 3294 = (212770579517124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3294 = 212770579517124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3294 = (5647:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3295) ≤ val WuPaper.ClassicalFourthData.Bq 3295
    have hp : val WuPaper.ClassicalFourthData.Bq 3295 = (212800290696719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3295 = 212800290696719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3295 = (2259:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_205
