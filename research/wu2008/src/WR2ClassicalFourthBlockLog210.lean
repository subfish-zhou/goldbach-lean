import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints210
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_210 (j : Fin 16) (hj : 16*210+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*210+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*210+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3360) ≤ val WuPaper.ClassicalFourthData.Bq 3360
    have hp : val WuPaper.ClassicalFourthData.Bq 3360 = (214706187190456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3360 = 214706187190456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3360 = (71:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3361) ≤ val WuPaper.ClassicalFourthData.Bq 3361
    have hp : val WuPaper.ClassicalFourthData.Bq 3361 = (214735122597194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3361 = 214735122597194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3361 = (11361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3362) ≤ val WuPaper.ClassicalFourthData.Bq 3362
    have hp : val WuPaper.ClassicalFourthData.Bq 3362 = (214764046413286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3362 = 214764046413286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3362 = (5681:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3363) ≤ val WuPaper.ClassicalFourthData.Bq 3363
    have hp : val WuPaper.ClassicalFourthData.Bq 3363 = (214792958643559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3363 = 214792958643559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3363 = (11363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3364) ≤ val WuPaper.ClassicalFourthData.Bq 3364
    have hp : val WuPaper.ClassicalFourthData.Bq 3364 = (214821859292834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3364 = 214821859292834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3364 = (2841:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3365) ≤ val WuPaper.ClassicalFourthData.Bq 3365
    have hp : val WuPaper.ClassicalFourthData.Bq 3365 = (214850748365932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3365 = 214850748365932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3365 = (2273:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3366) ≤ val WuPaper.ClassicalFourthData.Bq 3366
    have hp : val WuPaper.ClassicalFourthData.Bq 3366 = (214879625867670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3366 = 214879625867670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3366 = (5683:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3367) ≤ val WuPaper.ClassicalFourthData.Bq 3367
    have hp : val WuPaper.ClassicalFourthData.Bq 3367 = (214908491802863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3367 = 214908491802863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3367 = (11367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3367
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3368) ≤ val WuPaper.ClassicalFourthData.Bq 3368
    have hp : val WuPaper.ClassicalFourthData.Bq 3368 = (214937346176325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3368 = 214937346176325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3368 = (1421:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3369) ≤ val WuPaper.ClassicalFourthData.Bq 3369
    have hp : val WuPaper.ClassicalFourthData.Bq 3369 = (214966188992866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3369 = 214966188992866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3369 = (11369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3370) ≤ val WuPaper.ClassicalFourthData.Bq 3370
    have hp : val WuPaper.ClassicalFourthData.Bq 3370 = (214995020257293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3370 = 214995020257293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3370 = (1137:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3371) ≤ val WuPaper.ClassicalFourthData.Bq 3371
    have hp : val WuPaper.ClassicalFourthData.Bq 3371 = (215023839974413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3371 = 215023839974413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3371 = (11371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3372) ≤ val WuPaper.ClassicalFourthData.Bq 3372
    have hp : val WuPaper.ClassicalFourthData.Bq 3372 = (215052648149028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3372 = 215052648149028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3372 = (2843:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3373) ≤ val WuPaper.ClassicalFourthData.Bq 3373
    have hp : val WuPaper.ClassicalFourthData.Bq 3373 = (215081444785940:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3373 = 215081444785940 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3373 = (11373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3374) ≤ val WuPaper.ClassicalFourthData.Bq 3374
    have hp : val WuPaper.ClassicalFourthData.Bq 3374 = (215110229889947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3374 = 215110229889947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3374 = (5687:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3375) ≤ val WuPaper.ClassicalFourthData.Bq 3375
    have hp : val WuPaper.ClassicalFourthData.Bq 3375 = (215139003465844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3375 = 215139003465844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3375 = (91:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_210
