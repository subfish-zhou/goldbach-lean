import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints394
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_394 (j : Fin 16) (hj : 16*394+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*394+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*394+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6304) ≤ val WuPaper.ClassicalFourthData.Bq 6304
    have hp : val WuPaper.ClassicalFourthData.Bq 6304 = (264607888210892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6304 = 264607888210892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6304 = (447:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6305) ≤ val WuPaper.ClassicalFourthData.Bq 6305
    have hp : val WuPaper.ClassicalFourthData.Bq 6305 = (264616526591422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6305 = 264616526591422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6305 = (2861:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6306) ≤ val WuPaper.ClassicalFourthData.Bq 6306
    have hp : val WuPaper.ClassicalFourthData.Bq 6306 = (264625161131325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6306 = 264625161131325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6306 = (7153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6307) ≤ val WuPaper.ClassicalFourthData.Bq 6307
    have hp : val WuPaper.ClassicalFourthData.Bq 6307 = (264633791831916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6307 = 264633791831916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6307 = (14307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6308) ≤ val WuPaper.ClassicalFourthData.Bq 6308
    have hp : val WuPaper.ClassicalFourthData.Bq 6308 = (264642418694512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6308 = 264642418694512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6308 = (3577:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6309) ≤ val WuPaper.ClassicalFourthData.Bq 6309
    have hp : val WuPaper.ClassicalFourthData.Bq 6309 = (264651041720427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6309 = 264651041720427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6309 = (14309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6310) ≤ val WuPaper.ClassicalFourthData.Bq 6310
    have hp : val WuPaper.ClassicalFourthData.Bq 6310 = (264659660910977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6310 = 264659660910977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6310 = (1431:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6311) ≤ val WuPaper.ClassicalFourthData.Bq 6311
    have hp : val WuPaper.ClassicalFourthData.Bq 6311 = (264668276267475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6311 = 264668276267475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6311 = (14311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6312) ≤ val WuPaper.ClassicalFourthData.Bq 6312
    have hp : val WuPaper.ClassicalFourthData.Bq 6312 = (264676887791235:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6312 = 264676887791235 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6312 = (1789:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6313) ≤ val WuPaper.ClassicalFourthData.Bq 6313
    have hp : val WuPaper.ClassicalFourthData.Bq 6313 = (264685495483570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6313 = 264685495483570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6313 = (14313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6314) ≤ val WuPaper.ClassicalFourthData.Bq 6314
    have hp : val WuPaper.ClassicalFourthData.Bq 6314 = (264694099345793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6314 = 264694099345793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6314 = (7157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6315) ≤ val WuPaper.ClassicalFourthData.Bq 6315
    have hp : val WuPaper.ClassicalFourthData.Bq 6315 = (264702699379215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6315 = 264702699379215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6315 = (2863:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6316) ≤ val WuPaper.ClassicalFourthData.Bq 6316
    have hp : val WuPaper.ClassicalFourthData.Bq 6316 = (264711295585150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6316 = 264711295585150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6316 = (3579:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6317) ≤ val WuPaper.ClassicalFourthData.Bq 6317
    have hp : val WuPaper.ClassicalFourthData.Bq 6317 = (264719887964906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6317 = 264719887964906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6317 = (14317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6318) ≤ val WuPaper.ClassicalFourthData.Bq 6318
    have hp : val WuPaper.ClassicalFourthData.Bq 6318 = (264728476519796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6318 = 264728476519796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6318 = (7159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6319) ≤ val WuPaper.ClassicalFourthData.Bq 6319
    have hp : val WuPaper.ClassicalFourthData.Bq 6319 = (264737061251129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6319 = 264737061251129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6319 = (14319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_394
