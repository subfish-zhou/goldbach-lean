import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints460
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_460 (j : Fin 16) (hj : 16*460+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*460+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*460+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7360) ≤ val WuPaper.ClassicalFourthData.Bq 7360
    have hp : val WuPaper.ClassicalFourthData.Bq 7360 = (271823971920243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7360 = 271823971920243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7360 = (96:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7361) ≤ val WuPaper.ClassicalFourthData.Bq 7361
    have hp : val WuPaper.ClassicalFourthData.Bq 7361 = (271829197700279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7361 = 271829197700279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7361 = (15361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7362) ≤ val WuPaper.ClassicalFourthData.Bq 7362
    have hp : val WuPaper.ClassicalFourthData.Bq 7362 = (271834420782623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7362 = 271834420782623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7362 = (7681:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7363) ≤ val WuPaper.ClassicalFourthData.Bq 7363
    have hp : val WuPaper.ClassicalFourthData.Bq 7363 = (271839641168158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7363 = 271839641168158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7363 = (15363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7364) ≤ val WuPaper.ClassicalFourthData.Bq 7364
    have hp : val WuPaper.ClassicalFourthData.Bq 7364 = (271844858857765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7364 = 271844858857765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7364 = (3841:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7365) ≤ val WuPaper.ClassicalFourthData.Bq 7365
    have hp : val WuPaper.ClassicalFourthData.Bq 7365 = (271850073852324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7365 = 271850073852324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7365 = (3073:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7366) ≤ val WuPaper.ClassicalFourthData.Bq 7366
    have hp : val WuPaper.ClassicalFourthData.Bq 7366 = (271855286152718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7366 = 271855286152718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7366 = (7683:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7367) ≤ val WuPaper.ClassicalFourthData.Bq 7367
    have hp : val WuPaper.ClassicalFourthData.Bq 7367 = (271860495759826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7367 = 271860495759826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7367 = (15367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7367
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7368) ≤ val WuPaper.ClassicalFourthData.Bq 7368
    have hp : val WuPaper.ClassicalFourthData.Bq 7368 = (271865702674528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7368 = 271865702674528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7368 = (1921:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7369) ≤ val WuPaper.ClassicalFourthData.Bq 7369
    have hp : val WuPaper.ClassicalFourthData.Bq 7369 = (271870906897706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7369 = 271870906897706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7369 = (15369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7370) ≤ val WuPaper.ClassicalFourthData.Bq 7370
    have hp : val WuPaper.ClassicalFourthData.Bq 7370 = (271876108430237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7370 = 271876108430237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7370 = (1537:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7371) ≤ val WuPaper.ClassicalFourthData.Bq 7371
    have hp : val WuPaper.ClassicalFourthData.Bq 7371 = (271881307273002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7371 = 271881307273002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7371 = (15371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7372) ≤ val WuPaper.ClassicalFourthData.Bq 7372
    have hp : val WuPaper.ClassicalFourthData.Bq 7372 = (271886503426879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7372 = 271886503426879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7372 = (3843:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7373) ≤ val WuPaper.ClassicalFourthData.Bq 7373
    have hp : val WuPaper.ClassicalFourthData.Bq 7373 = (271891696892748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7373 = 271891696892748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7373 = (15373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7374) ≤ val WuPaper.ClassicalFourthData.Bq 7374
    have hp : val WuPaper.ClassicalFourthData.Bq 7374 = (271896887671486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7374 = 271896887671486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7374 = (7687:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7375) ≤ val WuPaper.ClassicalFourthData.Bq 7375
    have hp : val WuPaper.ClassicalFourthData.Bq 7375 = (271902075763971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7375 = 271902075763971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7375 = (123:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_460
