import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints459
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_459 (j : Fin 16) (hj : 16*459+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*459+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*459+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7344) ≤ val WuPaper.ClassicalFourthData.Bq 7344
    have hp : val WuPaper.ClassicalFourthData.Bq 7344 = (271739991832762:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7344 = 271739991832762 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7344 = (959:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7345) ≤ val WuPaper.ClassicalFourthData.Bq 7345
    have hp : val WuPaper.ClassicalFourthData.Bq 7345 = (271745260896060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7345 = 271745260896060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7345 = (3069:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7346) ≤ val WuPaper.ClassicalFourthData.Bq 7346
    have hp : val WuPaper.ClassicalFourthData.Bq 7346 = (271750527247513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7346 = 271750527247513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7346 = (7673:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7347) ≤ val WuPaper.ClassicalFourthData.Bq 7347
    have hp : val WuPaper.ClassicalFourthData.Bq 7347 = (271755790888007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7347 = 271755790888007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7347 = (15347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7348) ≤ val WuPaper.ClassicalFourthData.Bq 7348
    have hp : val WuPaper.ClassicalFourthData.Bq 7348 = (271761051818430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7348 = 271761051818430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7348 = (3837:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7349) ≤ val WuPaper.ClassicalFourthData.Bq 7349
    have hp : val WuPaper.ClassicalFourthData.Bq 7349 = (271766310039667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7349 = 271766310039667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7349 = (15349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7350) ≤ val WuPaper.ClassicalFourthData.Bq 7350
    have hp : val WuPaper.ClassicalFourthData.Bq 7350 = (271771565552606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7350 = 271771565552606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7350 = (307:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7351) ≤ val WuPaper.ClassicalFourthData.Bq 7351
    have hp : val WuPaper.ClassicalFourthData.Bq 7351 = (271776818358131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7351 = 271776818358131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7351 = (15351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7351
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7352) ≤ val WuPaper.ClassicalFourthData.Bq 7352
    have hp : val WuPaper.ClassicalFourthData.Bq 7352 = (271782068457128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7352 = 271782068457128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7352 = (1919:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7353) ≤ val WuPaper.ClassicalFourthData.Bq 7353
    have hp : val WuPaper.ClassicalFourthData.Bq 7353 = (271787315850482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7353 = 271787315850482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7353 = (15353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7354) ≤ val WuPaper.ClassicalFourthData.Bq 7354
    have hp : val WuPaper.ClassicalFourthData.Bq 7354 = (271792560539078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7354 = 271792560539078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7354 = (7677:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7355) ≤ val WuPaper.ClassicalFourthData.Bq 7355
    have hp : val WuPaper.ClassicalFourthData.Bq 7355 = (271797802523801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7355 = 271797802523801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7355 = (3071:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7356) ≤ val WuPaper.ClassicalFourthData.Bq 7356
    have hp : val WuPaper.ClassicalFourthData.Bq 7356 = (271803041805534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7356 = 271803041805534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7356 = (3839:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7357) ≤ val WuPaper.ClassicalFourthData.Bq 7357
    have hp : val WuPaper.ClassicalFourthData.Bq 7357 = (271808278385162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7357 = 271808278385162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7357 = (15357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7358) ≤ val WuPaper.ClassicalFourthData.Bq 7358
    have hp : val WuPaper.ClassicalFourthData.Bq 7358 = (271813512263567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7358 = 271813512263567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7358 = (7679:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7359) ≤ val WuPaper.ClassicalFourthData.Bq 7359
    have hp : val WuPaper.ClassicalFourthData.Bq 7359 = (271818743441633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7359 = 271818743441633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7359 = (15359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_459
