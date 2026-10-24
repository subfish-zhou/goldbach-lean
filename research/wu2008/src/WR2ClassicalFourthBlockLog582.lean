import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints582
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_582 (j : Fin 16) (hj : 16*582+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*582+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*582+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9312) ≤ val WuPaper.ClassicalFourthData.Bq 9312
    have hp : val WuPaper.ClassicalFourthData.Bq 9312 = (277812274258280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9312 = 277812274258280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9312 = (541:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9313) ≤ val WuPaper.ClassicalFourthData.Bq 9313
    have hp : val WuPaper.ClassicalFourthData.Bq 9313 = (277813582940176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9313 = 277813582940176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9313 = (17313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9314) ≤ val WuPaper.ClassicalFourthData.Bq 9314
    have hp : val WuPaper.ClassicalFourthData.Bq 9314 = (277814890167403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9314 = 277814890167403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9314 = (8657:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9315) ≤ val WuPaper.ClassicalFourthData.Bq 9315
    have hp : val WuPaper.ClassicalFourthData.Bq 9315 = (277816195940408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9315 = 277816195940408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9315 = (3463:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9316) ≤ val WuPaper.ClassicalFourthData.Bq 9316
    have hp : val WuPaper.ClassicalFourthData.Bq 9316 = (277817500259639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9316 = 277817500259639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9316 = (4329:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9317) ≤ val WuPaper.ClassicalFourthData.Bq 9317
    have hp : val WuPaper.ClassicalFourthData.Bq 9317 = (277818803125543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9317 = 277818803125543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9317 = (17317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9318) ≤ val WuPaper.ClassicalFourthData.Bq 9318
    have hp : val WuPaper.ClassicalFourthData.Bq 9318 = (277820104538569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9318 = 277820104538569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9318 = (8659:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9319) ≤ val WuPaper.ClassicalFourthData.Bq 9319
    have hp : val WuPaper.ClassicalFourthData.Bq 9319 = (277821404499163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9319 = 277821404499163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9319 = (17319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9319
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9320) ≤ val WuPaper.ClassicalFourthData.Bq 9320
    have hp : val WuPaper.ClassicalFourthData.Bq 9320 = (277822703007772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9320 = 277822703007772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9320 = (433:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9321) ≤ val WuPaper.ClassicalFourthData.Bq 9321
    have hp : val WuPaper.ClassicalFourthData.Bq 9321 = (277824000064844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9321 = 277824000064844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9321 = (17321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9322) ≤ val WuPaper.ClassicalFourthData.Bq 9322
    have hp : val WuPaper.ClassicalFourthData.Bq 9322 = (277825295670825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9322 = 277825295670825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9322 = (8661:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9323) ≤ val WuPaper.ClassicalFourthData.Bq 9323
    have hp : val WuPaper.ClassicalFourthData.Bq 9323 = (277826589826161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9323 = 277826589826161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9323 = (17323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9324) ≤ val WuPaper.ClassicalFourthData.Bq 9324
    have hp : val WuPaper.ClassicalFourthData.Bq 9324 = (277827882531300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9324 = 277827882531300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9324 = (4331:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9325) ≤ val WuPaper.ClassicalFourthData.Bq 9325
    have hp : val WuPaper.ClassicalFourthData.Bq 9325 = (277829173786687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9325 = 277829173786687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9325 = (693:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9326) ≤ val WuPaper.ClassicalFourthData.Bq 9326
    have hp : val WuPaper.ClassicalFourthData.Bq 9326 = (277830463592769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9326 = 277830463592769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9326 = (8663:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9327) ≤ val WuPaper.ClassicalFourthData.Bq 9327
    have hp : val WuPaper.ClassicalFourthData.Bq 9327 = (277831751949992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9327 = 277831751949992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9327 = (17327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_582
