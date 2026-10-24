import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints278
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_278 (j : Fin 16) (hj : 16*278+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*278+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*278+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4448) ≤ val WuPaper.ClassicalFourthData.Bq 4448
    have hp : val WuPaper.ClassicalFourthData.Bq 4448 = (240242726813630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4448 = 240242726813630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4448 = (389:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4449) ≤ val WuPaper.ClassicalFourthData.Bq 4449
    have hp : val WuPaper.ClassicalFourthData.Bq 4449 = (240261460374590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4449 = 240261460374590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4449 = (12449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4450) ≤ val WuPaper.ClassicalFourthData.Bq 4450
    have hp : val WuPaper.ClassicalFourthData.Bq 4450 = (240280186425444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4450 = 240280186425444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4450 = (249:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4451) ≤ val WuPaper.ClassicalFourthData.Bq 4451
    have hp : val WuPaper.ClassicalFourthData.Bq 4451 = (240298904969065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4451 = 240298904969065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4451 = (12451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4452) ≤ val WuPaper.ClassicalFourthData.Bq 4452
    have hp : val WuPaper.ClassicalFourthData.Bq 4452 = (240317616008327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4452 = 240317616008327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4452 = (3113:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4453) ≤ val WuPaper.ClassicalFourthData.Bq 4453
    have hp : val WuPaper.ClassicalFourthData.Bq 4453 = (240336319546102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4453 = 240336319546102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4453 = (12453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4454) ≤ val WuPaper.ClassicalFourthData.Bq 4454
    have hp : val WuPaper.ClassicalFourthData.Bq 4454 = (240355015585261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4454 = 240355015585261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4454 = (6227:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4455) ≤ val WuPaper.ClassicalFourthData.Bq 4455
    have hp : val WuPaper.ClassicalFourthData.Bq 4455 = (240373704128673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4455 = 240373704128673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4455 = (2491:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4455
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4456) ≤ val WuPaper.ClassicalFourthData.Bq 4456
    have hp : val WuPaper.ClassicalFourthData.Bq 4456 = (240392385179206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4456 = 240392385179206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4456 = (1557:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4457) ≤ val WuPaper.ClassicalFourthData.Bq 4457
    have hp : val WuPaper.ClassicalFourthData.Bq 4457 = (240411058739727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4457 = 240411058739727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4457 = (12457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4458) ≤ val WuPaper.ClassicalFourthData.Bq 4458
    have hp : val WuPaper.ClassicalFourthData.Bq 4458 = (240429724813103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4458 = 240429724813103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4458 = (6229:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4459) ≤ val WuPaper.ClassicalFourthData.Bq 4459
    have hp : val WuPaper.ClassicalFourthData.Bq 4459 = (240448383402196:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4459 = 240448383402196 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4459 = (12459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4460) ≤ val WuPaper.ClassicalFourthData.Bq 4460
    have hp : val WuPaper.ClassicalFourthData.Bq 4460 = (240467034509869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4460 = 240467034509869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4460 = (623:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4461) ≤ val WuPaper.ClassicalFourthData.Bq 4461
    have hp : val WuPaper.ClassicalFourthData.Bq 4461 = (240485678138986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4461 = 240485678138986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4461 = (12461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4462) ≤ val WuPaper.ClassicalFourthData.Bq 4462
    have hp : val WuPaper.ClassicalFourthData.Bq 4462 = (240504314292405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4462 = 240504314292405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4462 = (6231:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4463) ≤ val WuPaper.ClassicalFourthData.Bq 4463
    have hp : val WuPaper.ClassicalFourthData.Bq 4463 = (240522942972986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4463 = 240522942972986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4463 = (12463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4463
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_278
