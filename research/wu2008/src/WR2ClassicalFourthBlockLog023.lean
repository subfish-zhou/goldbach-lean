import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints023
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_023 (j : Fin 16) (hj : 16*23+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*23+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*23+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 368) ≤ val WuPaper.ClassicalFourthData.Bq 368
    have hp : val WuPaper.ClassicalFourthData.Bq 368 = (42070209045275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 368 = 42070209045275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 368 = (523:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 369) ≤ val WuPaper.ClassicalFourthData.Bq 369
    have hp : val WuPaper.ClassicalFourthData.Bq 369 = (42174591396539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 369 = 42174591396539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 369 = (8369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 370) ≤ val WuPaper.ClassicalFourthData.Bq 370
    have hp : val WuPaper.ClassicalFourthData.Bq 370 = (42278923769467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 370 = 42278923769467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 370 = (837:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 371) ≤ val WuPaper.ClassicalFourthData.Bq 371
    have hp : val WuPaper.ClassicalFourthData.Bq 371 = (42383206193424:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 371 = 42383206193424 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 371 = (8371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 372) ≤ val WuPaper.ClassicalFourthData.Bq 372
    have hp : val WuPaper.ClassicalFourthData.Bq 372 = (42487438697756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 372 = 42487438697756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 372 = (2093:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 373) ≤ val WuPaper.ClassicalFourthData.Bq 373
    have hp : val WuPaper.ClassicalFourthData.Bq 373 = (42591621311785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 373 = 42591621311785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 373 = (8373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 374) ≤ val WuPaper.ClassicalFourthData.Bq 374
    have hp : val WuPaper.ClassicalFourthData.Bq 374 = (42695754064813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 374 = 42695754064813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 374 = (4187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 375) ≤ val WuPaper.ClassicalFourthData.Bq 375
    have hp : val WuPaper.ClassicalFourthData.Bq 375 = (42799836986120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 375 = 42799836986120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 375 = (67:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 376) ≤ val WuPaper.ClassicalFourthData.Bq 376
    have hp : val WuPaper.ClassicalFourthData.Bq 376 = (42903870104962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 376 = 42903870104962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 376 = (1047:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 377) ≤ val WuPaper.ClassicalFourthData.Bq 377
    have hp : val WuPaper.ClassicalFourthData.Bq 377 = (43007853450576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 377 = 43007853450576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 377 = (8377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 378) ≤ val WuPaper.ClassicalFourthData.Bq 378
    have hp : val WuPaper.ClassicalFourthData.Bq 378 = (43111787052176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 378 = 43111787052176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 378 = (4189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 379) ≤ val WuPaper.ClassicalFourthData.Bq 379
    have hp : val WuPaper.ClassicalFourthData.Bq 379 = (43215670938953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 379 = 43215670938953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 379 = (8379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 380) ≤ val WuPaper.ClassicalFourthData.Bq 380
    have hp : val WuPaper.ClassicalFourthData.Bq 380 = (43319505140079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 380 = 43319505140079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 380 = (419:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 381) ≤ val WuPaper.ClassicalFourthData.Bq 381
    have hp : val WuPaper.ClassicalFourthData.Bq 381 = (43423289684702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 381 = 43423289684702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 381 = (8381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 382) ≤ val WuPaper.ClassicalFourthData.Bq 382
    have hp : val WuPaper.ClassicalFourthData.Bq 382 = (43527024601950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 382 = 43527024601950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 382 = (4191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 383) ≤ val WuPaper.ClassicalFourthData.Bq 383
    have hp : val WuPaper.ClassicalFourthData.Bq 383 = (43630709920927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 383 = 43630709920927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 383 = (8383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_023
