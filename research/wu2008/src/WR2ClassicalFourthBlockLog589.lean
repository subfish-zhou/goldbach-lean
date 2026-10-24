import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints589
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_589 (j : Fin 16) (hj : 16*589+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*589+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*589+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9424) ≤ val WuPaper.ClassicalFourthData.Bq 9424
    have hp : val WuPaper.ClassicalFourthData.Bq 9424 = (277949905565273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9424 = 277949905565273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9424 = (1089:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9425) ≤ val WuPaper.ClassicalFourthData.Bq 9425
    have hp : val WuPaper.ClassicalFourthData.Bq 9425 = (277951054074599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9425 = 277951054074599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9425 = (697:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9426) ≤ val WuPaper.ClassicalFourthData.Bq 9426
    have hp : val WuPaper.ClassicalFourthData.Bq 9426 = (277952201178507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9426 = 277952201178507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9426 = (8713:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9427) ≤ val WuPaper.ClassicalFourthData.Bq 9427
    have hp : val WuPaper.ClassicalFourthData.Bq 9427 = (277953346877429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9427 = 277953346877429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9427 = (17427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9428) ≤ val WuPaper.ClassicalFourthData.Bq 9428
    have hp : val WuPaper.ClassicalFourthData.Bq 9428 = (277954491171797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9428 = 277954491171797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9428 = (4357:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9429) ≤ val WuPaper.ClassicalFourthData.Bq 9429
    have hp : val WuPaper.ClassicalFourthData.Bq 9429 = (277955634062042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9429 = 277955634062042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9429 = (17429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9430) ≤ val WuPaper.ClassicalFourthData.Bq 9430
    have hp : val WuPaper.ClassicalFourthData.Bq 9430 = (277956775548596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9430 = 277956775548596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9430 = (1743:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9431) ≤ val WuPaper.ClassicalFourthData.Bq 9431
    have hp : val WuPaper.ClassicalFourthData.Bq 9431 = (277957915631888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9431 = 277957915631888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9431 = (17431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9431
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9432) ≤ val WuPaper.ClassicalFourthData.Bq 9432
    have hp : val WuPaper.ClassicalFourthData.Bq 9432 = (277959054312351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9432 = 277959054312351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9432 = (2179:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9433) ≤ val WuPaper.ClassicalFourthData.Bq 9433
    have hp : val WuPaper.ClassicalFourthData.Bq 9433 = (277960191590415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9433 = 277960191590415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9433 = (17433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9434) ≤ val WuPaper.ClassicalFourthData.Bq 9434
    have hp : val WuPaper.ClassicalFourthData.Bq 9434 = (277961327466511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9434 = 277961327466511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9434 = (8717:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9435) ≤ val WuPaper.ClassicalFourthData.Bq 9435
    have hp : val WuPaper.ClassicalFourthData.Bq 9435 = (277962461941069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9435 = 277962461941069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9435 = (3487:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9436) ≤ val WuPaper.ClassicalFourthData.Bq 9436
    have hp : val WuPaper.ClassicalFourthData.Bq 9436 = (277963595014519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9436 = 277963595014519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9436 = (4359:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9437) ≤ val WuPaper.ClassicalFourthData.Bq 9437
    have hp : val WuPaper.ClassicalFourthData.Bq 9437 = (277964726687293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9437 = 277964726687293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9437 = (17437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9438) ≤ val WuPaper.ClassicalFourthData.Bq 9438
    have hp : val WuPaper.ClassicalFourthData.Bq 9438 = (277965856959819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9438 = 277965856959819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9438 = (8719:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9439) ≤ val WuPaper.ClassicalFourthData.Bq 9439
    have hp : val WuPaper.ClassicalFourthData.Bq 9439 = (277966985832528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9439 = 277966985832528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9439 = (17439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_589
