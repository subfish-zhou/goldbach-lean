import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints597
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_597 (j : Fin 16) (hj : 16*597+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*597+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*597+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9552) ≤ val WuPaper.ClassicalFourthData.Bq 9552
    have hp : val WuPaper.ClassicalFourthData.Bq 9552 = (278085637382888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9552 = 278085637382888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9552 = (1097:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9553) ≤ val WuPaper.ClassicalFourthData.Bq 9553
    have hp : val WuPaper.ClassicalFourthData.Bq 9553 = (278086609459436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9553 = 278086609459436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9553 = (17553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9554) ≤ val WuPaper.ClassicalFourthData.Bq 9554
    have hp : val WuPaper.ClassicalFourthData.Bq 9554 = (278087580184685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9554 = 278087580184685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9554 = (8777:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9555) ≤ val WuPaper.ClassicalFourthData.Bq 9555
    have hp : val WuPaper.ClassicalFourthData.Bq 9555 = (278088549559049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9555 = 278088549559049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9555 = (3511:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9556) ≤ val WuPaper.ClassicalFourthData.Bq 9556
    have hp : val WuPaper.ClassicalFourthData.Bq 9556 = (278089517582941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9556 = 278089517582941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9556 = (4389:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9557) ≤ val WuPaper.ClassicalFourthData.Bq 9557
    have hp : val WuPaper.ClassicalFourthData.Bq 9557 = (278090484256776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9557 = 278090484256776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9557 = (17557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9558) ≤ val WuPaper.ClassicalFourthData.Bq 9558
    have hp : val WuPaper.ClassicalFourthData.Bq 9558 = (278091449580967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9558 = 278091449580967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9558 = (8779:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9559) ≤ val WuPaper.ClassicalFourthData.Bq 9559
    have hp : val WuPaper.ClassicalFourthData.Bq 9559 = (278092413555927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9559 = 278092413555927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9559 = (17559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9559
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9560) ≤ val WuPaper.ClassicalFourthData.Bq 9560
    have hp : val WuPaper.ClassicalFourthData.Bq 9560 = (278093376182069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9560 = 278093376182069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9560 = (439:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9561) ≤ val WuPaper.ClassicalFourthData.Bq 9561
    have hp : val WuPaper.ClassicalFourthData.Bq 9561 = (278094337459808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9561 = 278094337459808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9561 = (17561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9562) ≤ val WuPaper.ClassicalFourthData.Bq 9562
    have hp : val WuPaper.ClassicalFourthData.Bq 9562 = (278095297389555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9562 = 278095297389555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9562 = (8781:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9563) ≤ val WuPaper.ClassicalFourthData.Bq 9563
    have hp : val WuPaper.ClassicalFourthData.Bq 9563 = (278096255971724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9563 = 278096255971724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9563 = (17563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9564) ≤ val WuPaper.ClassicalFourthData.Bq 9564
    have hp : val WuPaper.ClassicalFourthData.Bq 9564 = (278097213206727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9564 = 278097213206727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9564 = (4391:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9565) ≤ val WuPaper.ClassicalFourthData.Bq 9565
    have hp : val WuPaper.ClassicalFourthData.Bq 9565 = (278098169094978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9565 = 278098169094978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9565 = (3513:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9566) ≤ val WuPaper.ClassicalFourthData.Bq 9566
    have hp : val WuPaper.ClassicalFourthData.Bq 9566 = (278099123636888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9566 = 278099123636888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9566 = (8783:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9567) ≤ val WuPaper.ClassicalFourthData.Bq 9567
    have hp : val WuPaper.ClassicalFourthData.Bq 9567 = (278100076832869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9567 = 278100076832869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9567 = (17567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_597
