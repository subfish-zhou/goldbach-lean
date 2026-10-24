import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints035
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_035 (j : Fin 16) (hj : 16*35+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*35+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*35+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 560) ≤ val WuPaper.ClassicalFourthData.Bq 560
    have hp : val WuPaper.ClassicalFourthData.Bq 560 = (61228160002993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 560 = 61228160002993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 560 = (107:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 561) ≤ val WuPaper.ClassicalFourthData.Bq 561
    have hp : val WuPaper.ClassicalFourthData.Bq 561 = (61323460628279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 561 = 61323460628279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 561 = (8561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 562) ≤ val WuPaper.ClassicalFourthData.Bq 562
    have hp : val WuPaper.ClassicalFourthData.Bq 562 = (61418716534598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 562 = 61418716534598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 562 = (4281:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 563) ≤ val WuPaper.ClassicalFourthData.Bq 563
    have hp : val WuPaper.ClassicalFourthData.Bq 563 = (61513927747460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 563 = 61513927747460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 563 = (8563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 564) ≤ val WuPaper.ClassicalFourthData.Bq 564
    have hp : val WuPaper.ClassicalFourthData.Bq 564 = (61609094292359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 564 = 61609094292359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 564 = (2141:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 565) ≤ val WuPaper.ClassicalFourthData.Bq 565
    have hp : val WuPaper.ClassicalFourthData.Bq 565 = (61704216194766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 565 = 61704216194766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 565 = (1713:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 566) ≤ val WuPaper.ClassicalFourthData.Bq 566
    have hp : val WuPaper.ClassicalFourthData.Bq 566 = (61799293480137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 566 = 61799293480137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 566 = (4283:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 567) ≤ val WuPaper.ClassicalFourthData.Bq 567
    have hp : val WuPaper.ClassicalFourthData.Bq 567 = (61894326173910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 567 = 61894326173910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 567 = (8567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_567
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 568) ≤ val WuPaper.ClassicalFourthData.Bq 568
    have hp : val WuPaper.ClassicalFourthData.Bq 568 = (61989314301503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 568 = 61989314301503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 568 = (1071:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 569) ≤ val WuPaper.ClassicalFourthData.Bq 569
    have hp : val WuPaper.ClassicalFourthData.Bq 569 = (62084257888316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 569 = 62084257888316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 569 = (8569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 570) ≤ val WuPaper.ClassicalFourthData.Bq 570
    have hp : val WuPaper.ClassicalFourthData.Bq 570 = (62179156959731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 570 = 62179156959731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 570 = (857:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 571) ≤ val WuPaper.ClassicalFourthData.Bq 571
    have hp : val WuPaper.ClassicalFourthData.Bq 571 = (62274011541112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 571 = 62274011541112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 571 = (8571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 572) ≤ val WuPaper.ClassicalFourthData.Bq 572
    have hp : val WuPaper.ClassicalFourthData.Bq 572 = (62368821657804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 572 = 62368821657804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 572 = (2143:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 573) ≤ val WuPaper.ClassicalFourthData.Bq 573
    have hp : val WuPaper.ClassicalFourthData.Bq 573 = (62463587335135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 573 = 62463587335135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 573 = (8573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 574) ≤ val WuPaper.ClassicalFourthData.Bq 574
    have hp : val WuPaper.ClassicalFourthData.Bq 574 = (62558308598414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 574 = 62558308598414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 574 = (4287:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 575) ≤ val WuPaper.ClassicalFourthData.Bq 575
    have hp : val WuPaper.ClassicalFourthData.Bq 575 = (62652985472931:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 575 = 62652985472931 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 575 = (343:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_035
