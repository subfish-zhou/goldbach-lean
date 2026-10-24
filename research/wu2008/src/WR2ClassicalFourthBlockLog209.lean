import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints209
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_209 (j : Fin 16) (hj : 16*209+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*209+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*209+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3344) ≤ val WuPaper.ClassicalFourthData.Bq 3344
    have hp : val WuPaper.ClassicalFourthData.Bq 3344 = (214241640408427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3344 = 214241640408427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3344 = (709:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3345) ≤ val WuPaper.ClassicalFourthData.Bq 3345
    have hp : val WuPaper.ClassicalFourthData.Bq 3345 = (214270761923650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3345 = 214270761923650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3345 = (2269:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3346) ≤ val WuPaper.ClassicalFourthData.Bq 3346
    have hp : val WuPaper.ClassicalFourthData.Bq 3346 = (214299871770699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3346 = 214299871770699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3346 = (5673:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3347) ≤ val WuPaper.ClassicalFourthData.Bq 3347
    have hp : val WuPaper.ClassicalFourthData.Bq 3347 = (214328969954438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3347 = 214328969954438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3347 = (11347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3348) ≤ val WuPaper.ClassicalFourthData.Bq 3348
    have hp : val WuPaper.ClassicalFourthData.Bq 3348 = (214358056479729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3348 = 214358056479729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3348 = (2837:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3349) ≤ val WuPaper.ClassicalFourthData.Bq 3349
    have hp : val WuPaper.ClassicalFourthData.Bq 3349 = (214387131351430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3349 = 214387131351430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3349 = (11349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3350) ≤ val WuPaper.ClassicalFourthData.Bq 3350
    have hp : val WuPaper.ClassicalFourthData.Bq 3350 = (214416194574399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3350 = 214416194574399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3350 = (227:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3351) ≤ val WuPaper.ClassicalFourthData.Bq 3351
    have hp : val WuPaper.ClassicalFourthData.Bq 3351 = (214445246153488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3351 = 214445246153488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3351 = (11351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3351
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3352) ≤ val WuPaper.ClassicalFourthData.Bq 3352
    have hp : val WuPaper.ClassicalFourthData.Bq 3352 = (214474286093551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3352 = 214474286093551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3352 = (1419:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3353) ≤ val WuPaper.ClassicalFourthData.Bq 3353
    have hp : val WuPaper.ClassicalFourthData.Bq 3353 = (214503314399435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3353 = 214503314399435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3353 = (11353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3354) ≤ val WuPaper.ClassicalFourthData.Bq 3354
    have hp : val WuPaper.ClassicalFourthData.Bq 3354 = (214532331075988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3354 = 214532331075988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3354 = (5677:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3355) ≤ val WuPaper.ClassicalFourthData.Bq 3355
    have hp : val WuPaper.ClassicalFourthData.Bq 3355 = (214561336128053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3355 = 214561336128053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3355 = (2271:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3356) ≤ val WuPaper.ClassicalFourthData.Bq 3356
    have hp : val WuPaper.ClassicalFourthData.Bq 3356 = (214590329560474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3356 = 214590329560474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3356 = (2839:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3357) ≤ val WuPaper.ClassicalFourthData.Bq 3357
    have hp : val WuPaper.ClassicalFourthData.Bq 3357 = (214619311378089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3357 = 214619311378089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3357 = (11357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3358) ≤ val WuPaper.ClassicalFourthData.Bq 3358
    have hp : val WuPaper.ClassicalFourthData.Bq 3358 = (214648281585735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3358 = 214648281585735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3358 = (5679:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3359) ≤ val WuPaper.ClassicalFourthData.Bq 3359
    have hp : val WuPaper.ClassicalFourthData.Bq 3359 = (214677240188246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3359 = 214677240188246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3359 = (11359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_209
