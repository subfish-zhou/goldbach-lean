import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints586
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_586 (j : Fin 16) (hj : 16*586+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*586+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*586+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9376) ≤ val WuPaper.ClassicalFourthData.Bq 9376
    have hp : val WuPaper.ClassicalFourthData.Bq 9376 = (277893115851036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9376 = 277893115851036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9376 = (543:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9377) ≤ val WuPaper.ClassicalFourthData.Bq 9377
    have hp : val WuPaper.ClassicalFourthData.Bq 9377 = (277894332330797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9377 = 277894332330797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9377 = (17377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9378) ≤ val WuPaper.ClassicalFourthData.Bq 9378
    have hp : val WuPaper.ClassicalFourthData.Bq 9378 = (277895547384254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9378 = 277895547384254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9378 = (8689:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9379) ≤ val WuPaper.ClassicalFourthData.Bq 9379
    have hp : val WuPaper.ClassicalFourthData.Bq 9379 = (277896761011845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9379 = 277896761011845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9379 = (17379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9380) ≤ val WuPaper.ClassicalFourthData.Bq 9380
    have hp : val WuPaper.ClassicalFourthData.Bq 9380 = (277897973214010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9380 = 277897973214010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9380 = (869:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9381) ≤ val WuPaper.ClassicalFourthData.Bq 9381
    have hp : val WuPaper.ClassicalFourthData.Bq 9381 = (277899183991186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9381 = 277899183991186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9381 = (17381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9382) ≤ val WuPaper.ClassicalFourthData.Bq 9382
    have hp : val WuPaper.ClassicalFourthData.Bq 9382 = (277900393343812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9382 = 277900393343812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9382 = (8691:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9383) ≤ val WuPaper.ClassicalFourthData.Bq 9383
    have hp : val WuPaper.ClassicalFourthData.Bq 9383 = (277901601272325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9383 = 277901601272325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9383 = (17383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9383
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9384) ≤ val WuPaper.ClassicalFourthData.Bq 9384
    have hp : val WuPaper.ClassicalFourthData.Bq 9384 = (277902807777163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9384 = 277902807777163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9384 = (2173:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9385) ≤ val WuPaper.ClassicalFourthData.Bq 9385
    have hp : val WuPaper.ClassicalFourthData.Bq 9385 = (277904012858764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9385 = 277904012858764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9385 = (3477:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9386) ≤ val WuPaper.ClassicalFourthData.Bq 9386
    have hp : val WuPaper.ClassicalFourthData.Bq 9386 = (277905216517565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9386 = 277905216517565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9386 = (8693:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9387) ≤ val WuPaper.ClassicalFourthData.Bq 9387
    have hp : val WuPaper.ClassicalFourthData.Bq 9387 = (277906418754004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9387 = 277906418754004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9387 = (17387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9388) ≤ val WuPaper.ClassicalFourthData.Bq 9388
    have hp : val WuPaper.ClassicalFourthData.Bq 9388 = (277907619568518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9388 = 277907619568518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9388 = (4347:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9389) ≤ val WuPaper.ClassicalFourthData.Bq 9389
    have hp : val WuPaper.ClassicalFourthData.Bq 9389 = (277908818961543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9389 = 277908818961543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9389 = (17389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9390) ≤ val WuPaper.ClassicalFourthData.Bq 9390
    have hp : val WuPaper.ClassicalFourthData.Bq 9390 = (277910016933517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9390 = 277910016933517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9390 = (1739:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9391) ≤ val WuPaper.ClassicalFourthData.Bq 9391
    have hp : val WuPaper.ClassicalFourthData.Bq 9391 = (277911213484877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9391 = 277911213484877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9391 = (17391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_586
