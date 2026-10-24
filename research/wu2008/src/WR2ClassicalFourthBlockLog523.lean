import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints523
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_523 (j : Fin 16) (hj : 16*523+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*523+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*523+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8368) ≤ val WuPaper.ClassicalFourthData.Bq 8368
    have hp : val WuPaper.ClassicalFourthData.Bq 8368 = (275859758243056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8368 = 275859758243056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8368 = (1023:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8369) ≤ val WuPaper.ClassicalFourthData.Bq 8369
    have hp : val WuPaper.ClassicalFourthData.Bq 8369 = (275862662661959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8369 = 275862662661959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8369 = (16369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8370) ≤ val WuPaper.ClassicalFourthData.Bq 8370
    have hp : val WuPaper.ClassicalFourthData.Bq 8370 = (275865565128879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8370 = 275865565128879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8370 = (1637:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8371) ≤ val WuPaper.ClassicalFourthData.Bq 8371
    have hp : val WuPaper.ClassicalFourthData.Bq 8371 = (275868465644431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8371 = 275868465644431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8371 = (16371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8372) ≤ val WuPaper.ClassicalFourthData.Bq 8372
    have hp : val WuPaper.ClassicalFourthData.Bq 8372 = (275871364209232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8372 = 275871364209232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8372 = (4093:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8373) ≤ val WuPaper.ClassicalFourthData.Bq 8373
    have hp : val WuPaper.ClassicalFourthData.Bq 8373 = (275874260823896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8373 = 275874260823896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8373 = (16373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8374) ≤ val WuPaper.ClassicalFourthData.Bq 8374
    have hp : val WuPaper.ClassicalFourthData.Bq 8374 = (275877155489039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8374 = 275877155489039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8374 = (8187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8375) ≤ val WuPaper.ClassicalFourthData.Bq 8375
    have hp : val WuPaper.ClassicalFourthData.Bq 8375 = (275880048205276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8375 = 275880048205276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8375 = (131:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8376) ≤ val WuPaper.ClassicalFourthData.Bq 8376
    have hp : val WuPaper.ClassicalFourthData.Bq 8376 = (275882938973222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8376 = 275882938973222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8376 = (2047:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8377) ≤ val WuPaper.ClassicalFourthData.Bq 8377
    have hp : val WuPaper.ClassicalFourthData.Bq 8377 = (275885827793491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8377 = 275885827793491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8377 = (16377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8378) ≤ val WuPaper.ClassicalFourthData.Bq 8378
    have hp : val WuPaper.ClassicalFourthData.Bq 8378 = (275888714666699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8378 = 275888714666699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8378 = (8189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8379) ≤ val WuPaper.ClassicalFourthData.Bq 8379
    have hp : val WuPaper.ClassicalFourthData.Bq 8379 = (275891599593458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8379 = 275891599593458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8379 = (16379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8380) ≤ val WuPaper.ClassicalFourthData.Bq 8380
    have hp : val WuPaper.ClassicalFourthData.Bq 8380 = (275894482574383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8380 = 275894482574383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8380 = (819:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8381) ≤ val WuPaper.ClassicalFourthData.Bq 8381
    have hp : val WuPaper.ClassicalFourthData.Bq 8381 = (275897363610088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8381 = 275897363610088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8381 = (16381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8382) ≤ val WuPaper.ClassicalFourthData.Bq 8382
    have hp : val WuPaper.ClassicalFourthData.Bq 8382 = (275900242701187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8382 = 275900242701187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8382 = (8191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8383) ≤ val WuPaper.ClassicalFourthData.Bq 8383
    have hp : val WuPaper.ClassicalFourthData.Bq 8383 = (275903119848292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8383 = 275903119848292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8383 = (16383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_523
