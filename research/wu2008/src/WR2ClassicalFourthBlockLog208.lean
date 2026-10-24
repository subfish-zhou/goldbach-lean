import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints208
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_208 (j : Fin 16) (hj : 16*208+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*208+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*208+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3328) ≤ val WuPaper.ClassicalFourthData.Bq 3328
    have hp : val WuPaper.ClassicalFourthData.Bq 3328 = (213774105314951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3328 = 213774105314951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3328 = (354:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3329) ≤ val WuPaper.ClassicalFourthData.Bq 3329
    have hp : val WuPaper.ClassicalFourthData.Bq 3329 = (213803414184420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3329 = 213803414184420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3329 = (11329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3330) ≤ val WuPaper.ClassicalFourthData.Bq 3330
    have hp : val WuPaper.ClassicalFourthData.Bq 3330 = (213832711307563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3330 = 213832711307563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3330 = (1133:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3331) ≤ val WuPaper.ClassicalFourthData.Bq 3331
    have hp : val WuPaper.ClassicalFourthData.Bq 3331 = (213861996689281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3331 = 213861996689281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3331 = (11331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3332) ≤ val WuPaper.ClassicalFourthData.Bq 3332
    have hp : val WuPaper.ClassicalFourthData.Bq 3332 = (213891270334476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3332 = 213891270334476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3332 = (2833:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3333) ≤ val WuPaper.ClassicalFourthData.Bq 3333
    have hp : val WuPaper.ClassicalFourthData.Bq 3333 = (213920532248045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3333 = 213920532248045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3333 = (11333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3334) ≤ val WuPaper.ClassicalFourthData.Bq 3334
    have hp : val WuPaper.ClassicalFourthData.Bq 3334 = (213949782434884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3334 = 213949782434884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3334 = (5667:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3335) ≤ val WuPaper.ClassicalFourthData.Bq 3335
    have hp : val WuPaper.ClassicalFourthData.Bq 3335 = (213979020899887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3335 = 213979020899887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3335 = (2267:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3335
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3336) ≤ val WuPaper.ClassicalFourthData.Bq 3336
    have hp : val WuPaper.ClassicalFourthData.Bq 3336 = (214008247647944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3336 = 214008247647944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3336 = (1417:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3337) ≤ val WuPaper.ClassicalFourthData.Bq 3337
    have hp : val WuPaper.ClassicalFourthData.Bq 3337 = (214037462683944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3337 = 214037462683944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3337 = (11337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3338) ≤ val WuPaper.ClassicalFourthData.Bq 3338
    have hp : val WuPaper.ClassicalFourthData.Bq 3338 = (214066666012772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3338 = 214066666012772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3338 = (5669:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3339) ≤ val WuPaper.ClassicalFourthData.Bq 3339
    have hp : val WuPaper.ClassicalFourthData.Bq 3339 = (214095857639311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3339 = 214095857639311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3339 = (11339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3340) ≤ val WuPaper.ClassicalFourthData.Bq 3340
    have hp : val WuPaper.ClassicalFourthData.Bq 3340 = (214125037568443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3340 = 214125037568443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3340 = (567:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3341) ≤ val WuPaper.ClassicalFourthData.Bq 3341
    have hp : val WuPaper.ClassicalFourthData.Bq 3341 = (214154205805045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3341 = 214154205805045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3341 = (11341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3342) ≤ val WuPaper.ClassicalFourthData.Bq 3342
    have hp : val WuPaper.ClassicalFourthData.Bq 3342 = (214183362353995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3342 = 214183362353995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3342 = (5671:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3343) ≤ val WuPaper.ClassicalFourthData.Bq 3343
    have hp : val WuPaper.ClassicalFourthData.Bq 3343 = (214212507220165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3343 = 214212507220165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3343 = (11343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3343
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_208
