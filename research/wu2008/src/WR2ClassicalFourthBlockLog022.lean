import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints022
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_022 (j : Fin 16) (hj : 16*22+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*22+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*22+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 352) ≤ val WuPaper.ClassicalFourthData.Bq 352
    have hp : val WuPaper.ClassicalFourthData.Bq 352 = (40393270322678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 352 = 40393270322678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 352 = (261:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 353) ≤ val WuPaper.ClassicalFourthData.Bq 353
    have hp : val WuPaper.ClassicalFourthData.Bq 353 = (40498456339170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 353 = 40498456339170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 353 = (8353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 354) ≤ val WuPaper.ClassicalFourthData.Bq 354
    have hp : val WuPaper.ClassicalFourthData.Bq 354 = (40603591904461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 354 = 40603591904461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 354 = (4177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 355) ≤ val WuPaper.ClassicalFourthData.Bq 355
    have hp : val WuPaper.ClassicalFourthData.Bq 355 = (40708677048271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 355 = 40708677048271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 355 = (1671:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 356) ≤ val WuPaper.ClassicalFourthData.Bq 356
    have hp : val WuPaper.ClassicalFourthData.Bq 356 = (40813711800299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 356 = 40813711800299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 356 = (2089:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 357) ≤ val WuPaper.ClassicalFourthData.Bq 357
    have hp : val WuPaper.ClassicalFourthData.Bq 357 = (40918696190219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 357 = 40918696190219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 357 = (8357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 358) ≤ val WuPaper.ClassicalFourthData.Bq 358
    have hp : val WuPaper.ClassicalFourthData.Bq 358 = (41023630247685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 358 = 41023630247685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 358 = (4179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 359) ≤ val WuPaper.ClassicalFourthData.Bq 359
    have hp : val WuPaper.ClassicalFourthData.Bq 359 = (41128514002328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 359 = 41128514002328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 359 = (8359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 360) ≤ val WuPaper.ClassicalFourthData.Bq 360
    have hp : val WuPaper.ClassicalFourthData.Bq 360 = (41233347483758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 360 = 41233347483758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 360 = (209:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 361) ≤ val WuPaper.ClassicalFourthData.Bq 361
    have hp : val WuPaper.ClassicalFourthData.Bq 361 = (41338130721560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 361 = 41338130721560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 361 = (8361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 362) ≤ val WuPaper.ClassicalFourthData.Bq 362
    have hp : val WuPaper.ClassicalFourthData.Bq 362 = (41442863745299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 362 = 41442863745299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 362 = (4181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 363) ≤ val WuPaper.ClassicalFourthData.Bq 363
    have hp : val WuPaper.ClassicalFourthData.Bq 363 = (41547546584519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 363 = 41547546584519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 363 = (8363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 364) ≤ val WuPaper.ClassicalFourthData.Bq 364
    have hp : val WuPaper.ClassicalFourthData.Bq 364 = (41652179268740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 364 = 41652179268740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 364 = (2091:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 365) ≤ val WuPaper.ClassicalFourthData.Bq 365
    have hp : val WuPaper.ClassicalFourthData.Bq 365 = (41756761827460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 365 = 41756761827460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 365 = (1673:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 366) ≤ val WuPaper.ClassicalFourthData.Bq 366
    have hp : val WuPaper.ClassicalFourthData.Bq 366 = (41861294290157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 366 = 41861294290157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 366 = (4183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 367) ≤ val WuPaper.ClassicalFourthData.Bq 367
    have hp : val WuPaper.ClassicalFourthData.Bq 367 = (41965776686284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 367 = 41965776686284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 367 = (8367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_022
