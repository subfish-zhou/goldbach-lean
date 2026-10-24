import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints408
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_408 (j : Fin 16) (hj : 16*408+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*408+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*408+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6528) ≤ val WuPaper.ClassicalFourthData.Bq 6528
    have hp : val WuPaper.ClassicalFourthData.Bq 6528 = (266449342913862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6528 = 266449342913862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6528 = (454:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6529) ≤ val WuPaper.ClassicalFourthData.Bq 6529
    have hp : val WuPaper.ClassicalFourthData.Bq 6529 = (266457152936832:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6529 = 266457152936832 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6529 = (14529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6530) ≤ val WuPaper.ClassicalFourthData.Bq 6530
    have hp : val WuPaper.ClassicalFourthData.Bq 6530 = (266464959401533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6530 = 266464959401533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6530 = (1453:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6531) ≤ val WuPaper.ClassicalFourthData.Bq 6531
    have hp : val WuPaper.ClassicalFourthData.Bq 6531 = (266472762309173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6531 = 266472762309173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6531 = (14531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6532) ≤ val WuPaper.ClassicalFourthData.Bq 6532
    have hp : val WuPaper.ClassicalFourthData.Bq 6532 = (266480561660955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6532 = 266480561660955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6532 = (3633:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6533) ≤ val WuPaper.ClassicalFourthData.Bq 6533
    have hp : val WuPaper.ClassicalFourthData.Bq 6533 = (266488357458086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6533 = 266488357458086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6533 = (14533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6534) ≤ val WuPaper.ClassicalFourthData.Bq 6534
    have hp : val WuPaper.ClassicalFourthData.Bq 6534 = (266496149701771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6534 = 266496149701771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6534 = (7267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6535) ≤ val WuPaper.ClassicalFourthData.Bq 6535
    have hp : val WuPaper.ClassicalFourthData.Bq 6535 = (266503938393214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6535 = 266503938393214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6535 = (2907:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6536) ≤ val WuPaper.ClassicalFourthData.Bq 6536
    have hp : val WuPaper.ClassicalFourthData.Bq 6536 = (266511723533618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6536 = 266511723533618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6536 = (1817:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6537) ≤ val WuPaper.ClassicalFourthData.Bq 6537
    have hp : val WuPaper.ClassicalFourthData.Bq 6537 = (266519505124187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6537 = 266519505124187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6537 = (14537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6538) ≤ val WuPaper.ClassicalFourthData.Bq 6538
    have hp : val WuPaper.ClassicalFourthData.Bq 6538 = (266527283166125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6538 = 266527283166125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6538 = (7269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6539) ≤ val WuPaper.ClassicalFourthData.Bq 6539
    have hp : val WuPaper.ClassicalFourthData.Bq 6539 = (266535057660634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6539 = 266535057660634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6539 = (14539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6540) ≤ val WuPaper.ClassicalFourthData.Bq 6540
    have hp : val WuPaper.ClassicalFourthData.Bq 6540 = (266542828608915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6540 = 266542828608915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6540 = (727:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6541) ≤ val WuPaper.ClassicalFourthData.Bq 6541
    have hp : val WuPaper.ClassicalFourthData.Bq 6541 = (266550596012170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6541 = 266550596012170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6541 = (14541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6542) ≤ val WuPaper.ClassicalFourthData.Bq 6542
    have hp : val WuPaper.ClassicalFourthData.Bq 6542 = (266558359871601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6542 = 266558359871601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6542 = (7271:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6543) ≤ val WuPaper.ClassicalFourthData.Bq 6543
    have hp : val WuPaper.ClassicalFourthData.Bq 6543 = (266566120188407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6543 = 266566120188407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6543 = (14543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_408
