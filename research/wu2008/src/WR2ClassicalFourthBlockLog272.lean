import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints272
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_272 (j : Fin 16) (hj : 16*272+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*272+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*272+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4352) ≤ val WuPaper.ClassicalFourthData.Bq 4352
    have hp : val WuPaper.ClassicalFourthData.Bq 4352 = (238408895731993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4352 = 238408895731993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4352 = (386:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4353) ≤ val WuPaper.ClassicalFourthData.Bq 4353
    have hp : val WuPaper.ClassicalFourthData.Bq 4353 = (238428363848095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4353 = 238428363848095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4353 = (12353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4354) ≤ val WuPaper.ClassicalFourthData.Bq 4354
    have hp : val WuPaper.ClassicalFourthData.Bq 4354 = (238447824171959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4354 = 238447824171959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4354 = (6177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4355) ≤ val WuPaper.ClassicalFourthData.Bq 4355
    have hp : val WuPaper.ClassicalFourthData.Bq 4355 = (238467276706586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4355 = 238467276706586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4355 = (2471:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4356) ≤ val WuPaper.ClassicalFourthData.Bq 4356
    have hp : val WuPaper.ClassicalFourthData.Bq 4356 = (238486721454979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4356 = 238486721454979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4356 = (3089:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4357) ≤ val WuPaper.ClassicalFourthData.Bq 4357
    have hp : val WuPaper.ClassicalFourthData.Bq 4357 = (238506158420138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4357 = 238506158420138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4357 = (12357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4358) ≤ val WuPaper.ClassicalFourthData.Bq 4358
    have hp : val WuPaper.ClassicalFourthData.Bq 4358 = (238525587605061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4358 = 238525587605061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4358 = (6179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4359) ≤ val WuPaper.ClassicalFourthData.Bq 4359
    have hp : val WuPaper.ClassicalFourthData.Bq 4359 = (238545009012745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4359 = 238545009012745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4359 = (12359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4360) ≤ val WuPaper.ClassicalFourthData.Bq 4360
    have hp : val WuPaper.ClassicalFourthData.Bq 4360 = (238564422646188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4360 = 238564422646188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4360 = (309:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4361) ≤ val WuPaper.ClassicalFourthData.Bq 4361
    have hp : val WuPaper.ClassicalFourthData.Bq 4361 = (238583828508383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4361 = 238583828508383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4361 = (12361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4362) ≤ val WuPaper.ClassicalFourthData.Bq 4362
    have hp : val WuPaper.ClassicalFourthData.Bq 4362 = (238603226602325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4362 = 238603226602325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4362 = (6181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4363) ≤ val WuPaper.ClassicalFourthData.Bq 4363
    have hp : val WuPaper.ClassicalFourthData.Bq 4363 = (238622616931004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4363 = 238622616931004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4363 = (12363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4364) ≤ val WuPaper.ClassicalFourthData.Bq 4364
    have hp : val WuPaper.ClassicalFourthData.Bq 4364 = (238641999497411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4364 = 238641999497411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4364 = (3091:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4365) ≤ val WuPaper.ClassicalFourthData.Bq 4365
    have hp : val WuPaper.ClassicalFourthData.Bq 4365 = (238661374304536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4365 = 238661374304536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4365 = (2473:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4366) ≤ val WuPaper.ClassicalFourthData.Bq 4366
    have hp : val WuPaper.ClassicalFourthData.Bq 4366 = (238680741355367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4366 = 238680741355367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4366 = (6183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4367) ≤ val WuPaper.ClassicalFourthData.Bq 4367
    have hp : val WuPaper.ClassicalFourthData.Bq 4367 = (238700100652890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4367 = 238700100652890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4367 = (12367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_272
