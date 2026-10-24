import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints461
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_461 (j : Fin 16) (hj : 16*461+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*461+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*461+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7376) ≤ val WuPaper.ClassicalFourthData.Bq 7376
    have hp : val WuPaper.ClassicalFourthData.Bq 7376 = (271907261171081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7376 = 271907261171081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7376 = (961:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7377) ≤ val WuPaper.ClassicalFourthData.Bq 7377
    have hp : val WuPaper.ClassicalFourthData.Bq 7377 = (271912443893693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7377 = 271912443893693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7377 = (15377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7378) ≤ val WuPaper.ClassicalFourthData.Bq 7378
    have hp : val WuPaper.ClassicalFourthData.Bq 7378 = (271917623932685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7378 = 271917623932685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7378 = (7689:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7379) ≤ val WuPaper.ClassicalFourthData.Bq 7379
    have hp : val WuPaper.ClassicalFourthData.Bq 7379 = (271922801288933:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7379 = 271922801288933 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7379 = (15379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7380) ≤ val WuPaper.ClassicalFourthData.Bq 7380
    have hp : val WuPaper.ClassicalFourthData.Bq 7380 = (271927975963314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7380 = 271927975963314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7380 = (769:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7381) ≤ val WuPaper.ClassicalFourthData.Bq 7381
    have hp : val WuPaper.ClassicalFourthData.Bq 7381 = (271933147956702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7381 = 271933147956702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7381 = (15381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7382) ≤ val WuPaper.ClassicalFourthData.Bq 7382
    have hp : val WuPaper.ClassicalFourthData.Bq 7382 = (271938317269976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7382 = 271938317269976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7382 = (7691:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7383) ≤ val WuPaper.ClassicalFourthData.Bq 7383
    have hp : val WuPaper.ClassicalFourthData.Bq 7383 = (271943483904008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7383 = 271943483904008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7383 = (15383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7383
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7384) ≤ val WuPaper.ClassicalFourthData.Bq 7384
    have hp : val WuPaper.ClassicalFourthData.Bq 7384 = (271948647859676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7384 = 271948647859676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7384 = (1923:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7385) ≤ val WuPaper.ClassicalFourthData.Bq 7385
    have hp : val WuPaper.ClassicalFourthData.Bq 7385 = (271953809137853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7385 = 271953809137853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7385 = (3077:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7386) ≤ val WuPaper.ClassicalFourthData.Bq 7386
    have hp : val WuPaper.ClassicalFourthData.Bq 7386 = (271958967739414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7386 = 271958967739414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7386 = (7693:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7387) ≤ val WuPaper.ClassicalFourthData.Bq 7387
    have hp : val WuPaper.ClassicalFourthData.Bq 7387 = (271964123665233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7387 = 271964123665233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7387 = (15387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7388) ≤ val WuPaper.ClassicalFourthData.Bq 7388
    have hp : val WuPaper.ClassicalFourthData.Bq 7388 = (271969276916184:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7388 = 271969276916184 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7388 = (3847:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7389) ≤ val WuPaper.ClassicalFourthData.Bq 7389
    have hp : val WuPaper.ClassicalFourthData.Bq 7389 = (271974427493140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7389 = 271974427493140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7389 = (15389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7390) ≤ val WuPaper.ClassicalFourthData.Bq 7390
    have hp : val WuPaper.ClassicalFourthData.Bq 7390 = (271979575396975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7390 = 271979575396975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7390 = (1539:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7391) ≤ val WuPaper.ClassicalFourthData.Bq 7391
    have hp : val WuPaper.ClassicalFourthData.Bq 7391 = (271984720628562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7391 = 271984720628562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7391 = (15391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_461
