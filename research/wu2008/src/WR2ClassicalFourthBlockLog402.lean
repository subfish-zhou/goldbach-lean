import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints402
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_402 (j : Fin 16) (hj : 16*402+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*402+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*402+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6432) ≤ val WuPaper.ClassicalFourthData.Bq 6432
    have hp : val WuPaper.ClassicalFourthData.Bq 6432 = (265682828177513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6432 = 265682828177513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6432 = (451:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6433) ≤ val WuPaper.ClassicalFourthData.Bq 6433
    have hp : val WuPaper.ClassicalFourthData.Bq 6433 = (265690985482159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6433 = 265690985482159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6433 = (14433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6434) ≤ val WuPaper.ClassicalFourthData.Bq 6434
    have hp : val WuPaper.ClassicalFourthData.Bq 6434 = (265699139110536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6434 = 265699139110536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6434 = (7217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6435) ≤ val WuPaper.ClassicalFourthData.Bq 6435
    have hp : val WuPaper.ClassicalFourthData.Bq 6435 = (265707289063896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6435 = 265707289063896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6435 = (2887:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6436) ≤ val WuPaper.ClassicalFourthData.Bq 6436
    have hp : val WuPaper.ClassicalFourthData.Bq 6436 = (265715435343489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6436 = 265715435343489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6436 = (3609:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6437) ≤ val WuPaper.ClassicalFourthData.Bq 6437
    have hp : val WuPaper.ClassicalFourthData.Bq 6437 = (265723577950567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6437 = 265723577950567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6437 = (14437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6438) ≤ val WuPaper.ClassicalFourthData.Bq 6438
    have hp : val WuPaper.ClassicalFourthData.Bq 6438 = (265731716886381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6438 = 265731716886381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6438 = (7219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6439) ≤ val WuPaper.ClassicalFourthData.Bq 6439
    have hp : val WuPaper.ClassicalFourthData.Bq 6439 = (265739852152180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6439 = 265739852152180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6439 = (14439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6440) ≤ val WuPaper.ClassicalFourthData.Bq 6440
    have hp : val WuPaper.ClassicalFourthData.Bq 6440 = (265747983749214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6440 = 265747983749214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6440 = (361:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6441) ≤ val WuPaper.ClassicalFourthData.Bq 6441
    have hp : val WuPaper.ClassicalFourthData.Bq 6441 = (265756111678732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6441 = 265756111678732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6441 = (14441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6442) ≤ val WuPaper.ClassicalFourthData.Bq 6442
    have hp : val WuPaper.ClassicalFourthData.Bq 6442 = (265764235941983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6442 = 265764235941983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6442 = (7221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6443) ≤ val WuPaper.ClassicalFourthData.Bq 6443
    have hp : val WuPaper.ClassicalFourthData.Bq 6443 = (265772356540215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6443 = 265772356540215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6443 = (14443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6444) ≤ val WuPaper.ClassicalFourthData.Bq 6444
    have hp : val WuPaper.ClassicalFourthData.Bq 6444 = (265780473474675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6444 = 265780473474675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6444 = (3611:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6445) ≤ val WuPaper.ClassicalFourthData.Bq 6445
    have hp : val WuPaper.ClassicalFourthData.Bq 6445 = (265788586746611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6445 = 265788586746611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6445 = (2889:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6446) ≤ val WuPaper.ClassicalFourthData.Bq 6446
    have hp : val WuPaper.ClassicalFourthData.Bq 6446 = (265796696357269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6446 = 265796696357269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6446 = (7223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6447) ≤ val WuPaper.ClassicalFourthData.Bq 6447
    have hp : val WuPaper.ClassicalFourthData.Bq 6447 = (265804802307896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6447 = 265804802307896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6447 = (14447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_402
