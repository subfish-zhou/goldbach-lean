import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints457
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_457 (j : Fin 16) (hj : 16*457+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*457+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*457+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7312) ≤ val WuPaper.ClassicalFourthData.Bq 7312
    have hp : val WuPaper.ClassicalFourthData.Bq 7312 = (271569944627711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7312 = 271569944627711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7312 = (957:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7313) ≤ val WuPaper.ClassicalFourthData.Bq 7313
    have hp : val WuPaper.ClassicalFourthData.Bq 7313 = (271575300940375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7313 = 271575300940375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7313 = (15313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7314) ≤ val WuPaper.ClassicalFourthData.Bq 7314
    have hp : val WuPaper.ClassicalFourthData.Bq 7314 = (271580654512636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7314 = 271580654512636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7314 = (7657:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7315) ≤ val WuPaper.ClassicalFourthData.Bq 7315
    have hp : val WuPaper.ClassicalFourthData.Bq 7315 = (271586005345391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7315 = 271586005345391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7315 = (3063:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7316) ≤ val WuPaper.ClassicalFourthData.Bq 7316
    have hp : val WuPaper.ClassicalFourthData.Bq 7316 = (271591353439537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7316 = 271591353439537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7316 = (3829:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7317) ≤ val WuPaper.ClassicalFourthData.Bq 7317
    have hp : val WuPaper.ClassicalFourthData.Bq 7317 = (271596698795971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7317 = 271596698795971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7317 = (15317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7318) ≤ val WuPaper.ClassicalFourthData.Bq 7318
    have hp : val WuPaper.ClassicalFourthData.Bq 7318 = (271602041415590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7318 = 271602041415590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7318 = (7659:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7319) ≤ val WuPaper.ClassicalFourthData.Bq 7319
    have hp : val WuPaper.ClassicalFourthData.Bq 7319 = (271607381299289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7319 = 271607381299289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7319 = (15319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7319
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7320) ≤ val WuPaper.ClassicalFourthData.Bq 7320
    have hp : val WuPaper.ClassicalFourthData.Bq 7320 = (271612718447966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7320 = 271612718447966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7320 = (383:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7321) ≤ val WuPaper.ClassicalFourthData.Bq 7321
    have hp : val WuPaper.ClassicalFourthData.Bq 7321 = (271618052862514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7321 = 271618052862514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7321 = (15321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7322) ≤ val WuPaper.ClassicalFourthData.Bq 7322
    have hp : val WuPaper.ClassicalFourthData.Bq 7322 = (271623384543830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7322 = 271623384543830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7322 = (7661:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7323) ≤ val WuPaper.ClassicalFourthData.Bq 7323
    have hp : val WuPaper.ClassicalFourthData.Bq 7323 = (271628713492809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7323 = 271628713492809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7323 = (15323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7324) ≤ val WuPaper.ClassicalFourthData.Bq 7324
    have hp : val WuPaper.ClassicalFourthData.Bq 7324 = (271634039710344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7324 = 271634039710344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7324 = (3831:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7325) ≤ val WuPaper.ClassicalFourthData.Bq 7325
    have hp : val WuPaper.ClassicalFourthData.Bq 7325 = (271639363197331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7325 = 271639363197331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7325 = (613:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7326) ≤ val WuPaper.ClassicalFourthData.Bq 7326
    have hp : val WuPaper.ClassicalFourthData.Bq 7326 = (271644683954663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7326 = 271644683954663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7326 = (7663:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7327) ≤ val WuPaper.ClassicalFourthData.Bq 7327
    have hp : val WuPaper.ClassicalFourthData.Bq 7327 = (271650001983234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7327 = 271650001983234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7327 = (15327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_457
