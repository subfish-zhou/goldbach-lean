import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints029
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_029 (j : Fin 16) (hj : 16*29+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*29+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*29+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 464) ≤ val WuPaper.ClassicalFourthData.Bq 464
    have hp : val WuPaper.ClassicalFourthData.Bq 464 = (51867137976900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 464 = 51867137976900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 464 = (529:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 465) ≤ val WuPaper.ClassicalFourthData.Bq 465
    have hp : val WuPaper.ClassicalFourthData.Bq 465 = (51966853258629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 465 = 51966853258629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 465 = (1693:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 466) ≤ val WuPaper.ClassicalFourthData.Bq 466
    have hp : val WuPaper.ClassicalFourthData.Bq 466 = (52066521284232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 466 = 52066521284232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 466 = (4233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 467) ≤ val WuPaper.ClassicalFourthData.Bq 467
    have hp : val WuPaper.ClassicalFourthData.Bq 467 = (52166142081064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 467 = 52166142081064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 467 = (8467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 468) ≤ val WuPaper.ClassicalFourthData.Bq 468
    have hp : val WuPaper.ClassicalFourthData.Bq 468 = (52265715676459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 468 = 52265715676459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 468 = (2117:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 469) ≤ val WuPaper.ClassicalFourthData.Bq 469
    have hp : val WuPaper.ClassicalFourthData.Bq 469 = (52365242097733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 469 = 52365242097733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 469 = (8469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 470) ≤ val WuPaper.ClassicalFourthData.Bq 470
    have hp : val WuPaper.ClassicalFourthData.Bq 470 = (52464721372178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 470 = 52464721372178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 470 = (847:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 471) ≤ val WuPaper.ClassicalFourthData.Bq 471
    have hp : val WuPaper.ClassicalFourthData.Bq 471 = (52564153527071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 471 = 52564153527071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 471 = (8471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 472) ≤ val WuPaper.ClassicalFourthData.Bq 472
    have hp : val WuPaper.ClassicalFourthData.Bq 472 = (52663538589664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 472 = 52663538589664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 472 = (1059:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 473) ≤ val WuPaper.ClassicalFourthData.Bq 473
    have hp : val WuPaper.ClassicalFourthData.Bq 473 = (52762876587193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 473 = 52762876587193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 473 = (8473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 474) ≤ val WuPaper.ClassicalFourthData.Bq 474
    have hp : val WuPaper.ClassicalFourthData.Bq 474 = (52862167546872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 474 = 52862167546872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 474 = (4237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 475) ≤ val WuPaper.ClassicalFourthData.Bq 475
    have hp : val WuPaper.ClassicalFourthData.Bq 475 = (52961411495896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 475 = 52961411495896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 475 = (339:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 476) ≤ val WuPaper.ClassicalFourthData.Bq 476
    have hp : val WuPaper.ClassicalFourthData.Bq 476 = (53060608461439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 476 = 53060608461439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 476 = (2119:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 477) ≤ val WuPaper.ClassicalFourthData.Bq 477
    have hp : val WuPaper.ClassicalFourthData.Bq 477 = (53159758470657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 477 = 53159758470657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 477 = (8477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 478) ≤ val WuPaper.ClassicalFourthData.Bq 478
    have hp : val WuPaper.ClassicalFourthData.Bq 478 = (53258861550683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 478 = 53258861550683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 478 = (4239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 479) ≤ val WuPaper.ClassicalFourthData.Bq 479
    have hp : val WuPaper.ClassicalFourthData.Bq 479 = (53357917728635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 479 = 53357917728635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 479 = (8479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_029
