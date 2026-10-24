import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints280
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_280 (j : Fin 16) (hj : 16*280+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*280+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*280+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4480) ≤ val WuPaper.ClassicalFourthData.Bq 4480
    have hp : val WuPaper.ClassicalFourthData.Bq 4480 = (240838489962796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4480 = 240838489962796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4480 = (78:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4481) ≤ val WuPaper.ClassicalFourthData.Bq 4481
    have hp : val WuPaper.ClassicalFourthData.Bq 4481 = (240856984619718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4481 = 240856984619718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4481 = (12481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4482) ≤ val WuPaper.ClassicalFourthData.Bq 4482
    have hp : val WuPaper.ClassicalFourthData.Bq 4482 = (240875471857879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4482 = 240875471857879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4482 = (6241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4483) ≤ val WuPaper.ClassicalFourthData.Bq 4483
    have hp : val WuPaper.ClassicalFourthData.Bq 4483 = (240893951680112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4483 = 240893951680112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4483 = (12483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4484) ≤ val WuPaper.ClassicalFourthData.Bq 4484
    have hp : val WuPaper.ClassicalFourthData.Bq 4484 = (240912424089249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4484 = 240912424089249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4484 = (3121:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4485) ≤ val WuPaper.ClassicalFourthData.Bq 4485
    have hp : val WuPaper.ClassicalFourthData.Bq 4485 = (240930889088122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4485 = 240930889088122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4485 = (2497:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4486) ≤ val WuPaper.ClassicalFourthData.Bq 4486
    have hp : val WuPaper.ClassicalFourthData.Bq 4486 = (240949346679559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4486 = 240949346679559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4486 = (6243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4487) ≤ val WuPaper.ClassicalFourthData.Bq 4487
    have hp : val WuPaper.ClassicalFourthData.Bq 4487 = (240967796866389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4487 = 240967796866389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4487 = (12487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4488) ≤ val WuPaper.ClassicalFourthData.Bq 4488
    have hp : val WuPaper.ClassicalFourthData.Bq 4488 = (240986239651439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4488 = 240986239651439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4488 = (1561:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4489) ≤ val WuPaper.ClassicalFourthData.Bq 4489
    have hp : val WuPaper.ClassicalFourthData.Bq 4489 = (241004675037534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4489 = 241004675037534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4489 = (12489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4490) ≤ val WuPaper.ClassicalFourthData.Bq 4490
    have hp : val WuPaper.ClassicalFourthData.Bq 4490 = (241023103027499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4490 = 241023103027499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4490 = (1249:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4491) ≤ val WuPaper.ClassicalFourthData.Bq 4491
    have hp : val WuPaper.ClassicalFourthData.Bq 4491 = (241041523624157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4491 = 241041523624157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4491 = (12491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4492) ≤ val WuPaper.ClassicalFourthData.Bq 4492
    have hp : val WuPaper.ClassicalFourthData.Bq 4492 = (241059936830330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4492 = 241059936830330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4492 = (3123:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4493) ≤ val WuPaper.ClassicalFourthData.Bq 4493
    have hp : val WuPaper.ClassicalFourthData.Bq 4493 = (241078342648838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4493 = 241078342648838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4493 = (12493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4494) ≤ val WuPaper.ClassicalFourthData.Bq 4494
    have hp : val WuPaper.ClassicalFourthData.Bq 4494 = (241096741082501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4494 = 241096741082501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4494 = (6247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4495) ≤ val WuPaper.ClassicalFourthData.Bq 4495
    have hp : val WuPaper.ClassicalFourthData.Bq 4495 = (241115132134136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4495 = 241115132134136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4495 = (2499:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_280
