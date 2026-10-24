import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints524
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_524 (j : Fin 16) (hj : 16*524+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*524+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*524+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8384) ≤ val WuPaper.ClassicalFourthData.Bq 8384
    have hp : val WuPaper.ClassicalFourthData.Bq 8384 = (275905995052018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8384 = 275905995052018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8384 = (512:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8385) ≤ val WuPaper.ClassicalFourthData.Bq 8385
    have hp : val WuPaper.ClassicalFourthData.Bq 8385 = (275908868312976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8385 = 275908868312976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8385 = (3277:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8386) ≤ val WuPaper.ClassicalFourthData.Bq 8386
    have hp : val WuPaper.ClassicalFourthData.Bq 8386 = (275911739631779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8386 = 275911739631779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8386 = (8193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8387) ≤ val WuPaper.ClassicalFourthData.Bq 8387
    have hp : val WuPaper.ClassicalFourthData.Bq 8387 = (275914609009041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8387 = 275914609009041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8387 = (16387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8388) ≤ val WuPaper.ClassicalFourthData.Bq 8388
    have hp : val WuPaper.ClassicalFourthData.Bq 8388 = (275917476445373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8388 = 275917476445373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8388 = (4097:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8389) ≤ val WuPaper.ClassicalFourthData.Bq 8389
    have hp : val WuPaper.ClassicalFourthData.Bq 8389 = (275920341941388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8389 = 275920341941388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8389 = (16389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8390) ≤ val WuPaper.ClassicalFourthData.Bq 8390
    have hp : val WuPaper.ClassicalFourthData.Bq 8390 = (275923205497696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8390 = 275923205497696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8390 = (1639:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8391) ≤ val WuPaper.ClassicalFourthData.Bq 8391
    have hp : val WuPaper.ClassicalFourthData.Bq 8391 = (275926067114911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8391 = 275926067114911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8391 = (16391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8392) ≤ val WuPaper.ClassicalFourthData.Bq 8392
    have hp : val WuPaper.ClassicalFourthData.Bq 8392 = (275928926793643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8392 = 275928926793643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8392 = (2049:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8393) ≤ val WuPaper.ClassicalFourthData.Bq 8393
    have hp : val WuPaper.ClassicalFourthData.Bq 8393 = (275931784534504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8393 = 275931784534504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8393 = (16393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8394) ≤ val WuPaper.ClassicalFourthData.Bq 8394
    have hp : val WuPaper.ClassicalFourthData.Bq 8394 = (275934640338104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8394 = 275934640338104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8394 = (8197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8395) ≤ val WuPaper.ClassicalFourthData.Bq 8395
    have hp : val WuPaper.ClassicalFourthData.Bq 8395 = (275937494205055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8395 = 275937494205055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8395 = (3279:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8396) ≤ val WuPaper.ClassicalFourthData.Bq 8396
    have hp : val WuPaper.ClassicalFourthData.Bq 8396 = (275940346135967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8396 = 275940346135967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8396 = (4099:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8397) ≤ val WuPaper.ClassicalFourthData.Bq 8397
    have hp : val WuPaper.ClassicalFourthData.Bq 8397 = (275943196131450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8397 = 275943196131450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8397 = (16397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8398) ≤ val WuPaper.ClassicalFourthData.Bq 8398
    have hp : val WuPaper.ClassicalFourthData.Bq 8398 = (275946044192115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8398 = 275946044192115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8398 = (8199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8399) ≤ val WuPaper.ClassicalFourthData.Bq 8399
    have hp : val WuPaper.ClassicalFourthData.Bq 8399 = (275948890318572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8399 = 275948890318572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8399 = (16399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_524
