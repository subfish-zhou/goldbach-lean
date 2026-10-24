import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints020
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_020 (j : Fin 16) (hj : 16*20+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*20+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*20+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 320) ≤ val WuPaper.ClassicalFourthData.Bq 320
    have hp : val WuPaper.ClassicalFourthData.Bq 320 = (37000500546216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 320 = 37000500546216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 320 = (52:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 321) ≤ val WuPaper.ClassicalFourthData.Bq 321
    have hp : val WuPaper.ClassicalFourthData.Bq 321 = (37107316827259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 321 = 37107316827259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 321 = (8321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 322) ≤ val WuPaper.ClassicalFourthData.Bq 322
    have hp : val WuPaper.ClassicalFourthData.Bq 322 = (37214081694210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 322 = 37214081694210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 322 = (4161:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 323) ≤ val WuPaper.ClassicalFourthData.Bq 323
    have hp : val WuPaper.ClassicalFourthData.Bq 323 = (37320795177511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 323 = 37320795177511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 323 = (8323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 324) ≤ val WuPaper.ClassicalFourthData.Bq 324
    have hp : val WuPaper.ClassicalFourthData.Bq 324 = (37427457307579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 324 = 37427457307579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 324 = (2081:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 325) ≤ val WuPaper.ClassicalFourthData.Bq 325
    have hp : val WuPaper.ClassicalFourthData.Bq 325 = (37534068114812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 325 = 37534068114812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 325 = (333:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 326) ≤ val WuPaper.ClassicalFourthData.Bq 326
    have hp : val WuPaper.ClassicalFourthData.Bq 326 = (37640627629583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 326 = 37640627629583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 326 = (4163:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 327) ≤ val WuPaper.ClassicalFourthData.Bq 327
    have hp : val WuPaper.ClassicalFourthData.Bq 327 = (37747135882242:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 327 = 37747135882242 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 327 = (8327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_327
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 328) ≤ val WuPaper.ClassicalFourthData.Bq 328
    have hp : val WuPaper.ClassicalFourthData.Bq 328 = (37853592903118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 328 = 37853592903118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 328 = (1041:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_328
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 329) ≤ val WuPaper.ClassicalFourthData.Bq 329
    have hp : val WuPaper.ClassicalFourthData.Bq 329 = (37959998722514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 329 = 37959998722514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 329 = (8329:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_329
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 330) ≤ val WuPaper.ClassicalFourthData.Bq 330
    have hp : val WuPaper.ClassicalFourthData.Bq 330 = (38066353370713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 330 = 38066353370713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 330 = (833:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_330
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 331) ≤ val WuPaper.ClassicalFourthData.Bq 331
    have hp : val WuPaper.ClassicalFourthData.Bq 331 = (38172656877974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 331 = 38172656877974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 331 = (8331:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_331
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 332) ≤ val WuPaper.ClassicalFourthData.Bq 332
    have hp : val WuPaper.ClassicalFourthData.Bq 332 = (38278909274534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 332 = 38278909274534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 332 = (2083:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_332
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 333) ≤ val WuPaper.ClassicalFourthData.Bq 333
    have hp : val WuPaper.ClassicalFourthData.Bq 333 = (38385110590607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 333 = 38385110590607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 333 = (8333:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_333
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 334) ≤ val WuPaper.ClassicalFourthData.Bq 334
    have hp : val WuPaper.ClassicalFourthData.Bq 334 = (38491260856385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 334 = 38491260856385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 334 = (4167:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_334
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 335) ≤ val WuPaper.ClassicalFourthData.Bq 335
    have hp : val WuPaper.ClassicalFourthData.Bq 335 = (38597360102035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 335 = 38597360102035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 335 = (1667:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_335
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_020
