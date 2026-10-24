import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints648
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_648 (j : Fin 16) (hj : 16*648+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*648+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*648+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10368) ≤ val WuPaper.ClassicalFourthData.Bq 10368
    have hp : val WuPaper.ClassicalFourthData.Bq 10368 = (278464536281937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10368 = 278464536281937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10368 = (574:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10369) ≤ val WuPaper.ClassicalFourthData.Bq 10369
    have hp : val WuPaper.ClassicalFourthData.Bq 10369 = (278464532047281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10369 = 278464532047281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10369 = (18369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10370) ≤ val WuPaper.ClassicalFourthData.Bq 10370
    have hp : val WuPaper.ClassicalFourthData.Bq 10370 = (278464526758462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10370 = 278464526758462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10370 = (1837:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10371) ≤ val WuPaper.ClassicalFourthData.Bq 10371
    have hp : val WuPaper.ClassicalFourthData.Bq 10371 = (278464520415799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10371 = 278464520415799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10371 = (18371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10372) ≤ val WuPaper.ClassicalFourthData.Bq 10372
    have hp : val WuPaper.ClassicalFourthData.Bq 10372 = (278464513019611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10372 = 278464513019611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10372 = (4593:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10373) ≤ val WuPaper.ClassicalFourthData.Bq 10373
    have hp : val WuPaper.ClassicalFourthData.Bq 10373 = (278464504570216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10373 = 278464504570216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10373 = (18373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10374) ≤ val WuPaper.ClassicalFourthData.Bq 10374
    have hp : val WuPaper.ClassicalFourthData.Bq 10374 = (278464495067933:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10374 = 278464495067933 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10374 = (9187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10375) ≤ val WuPaper.ClassicalFourthData.Bq 10375
    have hp : val WuPaper.ClassicalFourthData.Bq 10375 = (278464484513080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10375 = 278464484513080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10375 = (147:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10376) ≤ val WuPaper.ClassicalFourthData.Bq 10376
    have hp : val WuPaper.ClassicalFourthData.Bq 10376 = (278464472905977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10376 = 278464472905977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10376 = (2297:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10377) ≤ val WuPaper.ClassicalFourthData.Bq 10377
    have hp : val WuPaper.ClassicalFourthData.Bq 10377 = (278464460246940:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10377 = 278464460246940 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10377 = (18377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10378) ≤ val WuPaper.ClassicalFourthData.Bq 10378
    have hp : val WuPaper.ClassicalFourthData.Bq 10378 = (278464446536289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10378 = 278464446536289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10378 = (9189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10379) ≤ val WuPaper.ClassicalFourthData.Bq 10379
    have hp : val WuPaper.ClassicalFourthData.Bq 10379 = (278464431774341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10379 = 278464431774341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10379 = (18379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10380) ≤ val WuPaper.ClassicalFourthData.Bq 10380
    have hp : val WuPaper.ClassicalFourthData.Bq 10380 = (278464415961415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10380 = 278464415961415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10380 = (919:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10381) ≤ val WuPaper.ClassicalFourthData.Bq 10381
    have hp : val WuPaper.ClassicalFourthData.Bq 10381 = (278464399097829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10381 = 278464399097829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10381 = (18381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10382) ≤ val WuPaper.ClassicalFourthData.Bq 10382
    have hp : val WuPaper.ClassicalFourthData.Bq 10382 = (278464381183899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10382 = 278464381183899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10382 = (9191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10383) ≤ val WuPaper.ClassicalFourthData.Bq 10383
    have hp : val WuPaper.ClassicalFourthData.Bq 10383 = (278464362219945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10383 = 278464362219945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10383 = (18383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_648
