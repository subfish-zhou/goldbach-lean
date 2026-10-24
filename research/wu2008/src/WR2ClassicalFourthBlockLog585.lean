import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints585
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_585 (j : Fin 16) (hj : 16*585+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*585+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*585+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9360) ≤ val WuPaper.ClassicalFourthData.Bq 9360
    have hp : val WuPaper.ClassicalFourthData.Bq 9360 = (277873457839200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9360 = 277873457839200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9360 = (217:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9361) ≤ val WuPaper.ClassicalFourthData.Bq 9361
    have hp : val WuPaper.ClassicalFourthData.Bq 9361 = (277874697199572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9361 = 277874697199572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9361 = (17361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9362) ≤ val WuPaper.ClassicalFourthData.Bq 9362
    have hp : val WuPaper.ClassicalFourthData.Bq 9362 = (277875935126605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9362 = 277875935126605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9362 = (8681:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9363) ≤ val WuPaper.ClassicalFourthData.Bq 9363
    have hp : val WuPaper.ClassicalFourthData.Bq 9363 = (277877171620739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9363 = 277877171620739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9363 = (17363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9364) ≤ val WuPaper.ClassicalFourthData.Bq 9364
    have hp : val WuPaper.ClassicalFourthData.Bq 9364 = (277878406682416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9364 = 277878406682416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9364 = (4341:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9365) ≤ val WuPaper.ClassicalFourthData.Bq 9365
    have hp : val WuPaper.ClassicalFourthData.Bq 9365 = (277879640312076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9365 = 277879640312076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9365 = (3473:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9366) ≤ val WuPaper.ClassicalFourthData.Bq 9366
    have hp : val WuPaper.ClassicalFourthData.Bq 9366 = (277880872510158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9366 = 277880872510158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9366 = (8683:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9367) ≤ val WuPaper.ClassicalFourthData.Bq 9367
    have hp : val WuPaper.ClassicalFourthData.Bq 9367 = (277882103277104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9367 = 277882103277104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9367 = (17367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9367
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9368) ≤ val WuPaper.ClassicalFourthData.Bq 9368
    have hp : val WuPaper.ClassicalFourthData.Bq 9368 = (277883332613354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9368 = 277883332613354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9368 = (2171:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9369) ≤ val WuPaper.ClassicalFourthData.Bq 9369
    have hp : val WuPaper.ClassicalFourthData.Bq 9369 = (277884560519347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9369 = 277884560519347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9369 = (17369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9370) ≤ val WuPaper.ClassicalFourthData.Bq 9370
    have hp : val WuPaper.ClassicalFourthData.Bq 9370 = (277885786995523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9370 = 277885786995523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9370 = (1737:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9371) ≤ val WuPaper.ClassicalFourthData.Bq 9371
    have hp : val WuPaper.ClassicalFourthData.Bq 9371 = (277887012042322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9371 = 277887012042322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9371 = (17371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9372) ≤ val WuPaper.ClassicalFourthData.Bq 9372
    have hp : val WuPaper.ClassicalFourthData.Bq 9372 = (277888235660183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9372 = 277888235660183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9372 = (4343:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9373) ≤ val WuPaper.ClassicalFourthData.Bq 9373
    have hp : val WuPaper.ClassicalFourthData.Bq 9373 = (277889457849546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9373 = 277889457849546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9373 = (17373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9374) ≤ val WuPaper.ClassicalFourthData.Bq 9374
    have hp : val WuPaper.ClassicalFourthData.Bq 9374 = (277890678610850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9374 = 277890678610850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9374 = (8687:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9375) ≤ val WuPaper.ClassicalFourthData.Bq 9375
    have hp : val WuPaper.ClassicalFourthData.Bq 9375 = (277891897944534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9375 = 277891897944534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9375 = (139:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_585
