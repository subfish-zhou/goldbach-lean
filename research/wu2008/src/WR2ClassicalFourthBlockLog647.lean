import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints647
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_647 (j : Fin 16) (hj : 16*647+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*647+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*647+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10352) ≤ val WuPaper.ClassicalFourthData.Bq 10352
    have hp : val WuPaper.ClassicalFourthData.Bq 10352 = (278464460409619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10352 = 278464460409619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10352 = (1147:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10353) ≤ val WuPaper.ClassicalFourthData.Bq 10353
    have hp : val WuPaper.ClassicalFourthData.Bq 10353 = (278464473085027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10353 = 278464473085027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10353 = (18353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10354) ≤ val WuPaper.ClassicalFourthData.Bq 10354
    have hp : val WuPaper.ClassicalFourthData.Bq 10354 = (278464484701157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10354 = 278464484701157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10354 = (9177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10355) ≤ val WuPaper.ClassicalFourthData.Bq 10355
    have hp : val WuPaper.ClassicalFourthData.Bq 10355 = (278464495258327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10355 = 278464495258327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10355 = (3671:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10356) ≤ val WuPaper.ClassicalFourthData.Bq 10356
    have hp : val WuPaper.ClassicalFourthData.Bq 10356 = (278464504756859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10356 = 278464504756859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10356 = (4589:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10357) ≤ val WuPaper.ClassicalFourthData.Bq 10357
    have hp : val WuPaper.ClassicalFourthData.Bq 10357 = (278464513197072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10357 = 278464513197072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10357 = (18357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10358) ≤ val WuPaper.ClassicalFourthData.Bq 10358
    have hp : val WuPaper.ClassicalFourthData.Bq 10358 = (278464520579288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10358 = 278464520579288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10358 = (9179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10359) ≤ val WuPaper.ClassicalFourthData.Bq 10359
    have hp : val WuPaper.ClassicalFourthData.Bq 10359 = (278464526903826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10359 = 278464526903826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10359 = (18359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10360) ≤ val WuPaper.ClassicalFourthData.Bq 10360
    have hp : val WuPaper.ClassicalFourthData.Bq 10360 = (278464532171006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10360 = 278464532171006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10360 = (459:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10361) ≤ val WuPaper.ClassicalFourthData.Bq 10361
    have hp : val WuPaper.ClassicalFourthData.Bq 10361 = (278464536381148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10361 = 278464536381148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10361 = (18361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10362) ≤ val WuPaper.ClassicalFourthData.Bq 10362
    have hp : val WuPaper.ClassicalFourthData.Bq 10362 = (278464539534573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10362 = 278464539534573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10362 = (9181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10363) ≤ val WuPaper.ClassicalFourthData.Bq 10363
    have hp : val WuPaper.ClassicalFourthData.Bq 10363 = (278464541631599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10363 = 278464541631599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10363 = (18363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10364) ≤ val WuPaper.ClassicalFourthData.Bq 10364
    have hp : val WuPaper.ClassicalFourthData.Bq 10364 = (278464542672546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10364 = 278464542672546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10364 = (4591:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10365) ≤ val WuPaper.ClassicalFourthData.Bq 10365
    have hp : val WuPaper.ClassicalFourthData.Bq 10365 = (278464542657734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10365 = 278464542657734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10365 = (3673:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10366) ≤ val WuPaper.ClassicalFourthData.Bq 10366
    have hp : val WuPaper.ClassicalFourthData.Bq 10366 = (278464541587482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10366 = 278464541587482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10366 = (9183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10367) ≤ val WuPaper.ClassicalFourthData.Bq 10367
    have hp : val WuPaper.ClassicalFourthData.Bq 10367 = (278464539462110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10367 = 278464539462110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10367 = (18367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_647
