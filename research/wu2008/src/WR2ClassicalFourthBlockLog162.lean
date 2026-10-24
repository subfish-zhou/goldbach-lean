import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints162
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_162 (j : Fin 16) (hj : 16*162+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*162+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*162+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2592) ≤ val WuPaper.ClassicalFourthData.Bq 2592
    have hp : val WuPaper.ClassicalFourthData.Bq 2592 = (188656507359245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2592 = 188656507359245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2592 = (331:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2593) ≤ val WuPaper.ClassicalFourthData.Bq 2593
    have hp : val WuPaper.ClassicalFourthData.Bq 2593 = (188695976214962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2593 = 188695976214962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2593 = (10593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2594) ≤ val WuPaper.ClassicalFourthData.Bq 2594
    have hp : val WuPaper.ClassicalFourthData.Bq 2594 = (188735428933226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2594 = 188735428933226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2594 = (5297:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2595) ≤ val WuPaper.ClassicalFourthData.Bq 2595
    have hp : val WuPaper.ClassicalFourthData.Bq 2595 = (188774865521242:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2595 = 188774865521242 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2595 = (2119:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2596) ≤ val WuPaper.ClassicalFourthData.Bq 2596
    have hp : val WuPaper.ClassicalFourthData.Bq 2596 = (188814285986207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2596 = 188814285986207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2596 = (2649:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2597) ≤ val WuPaper.ClassicalFourthData.Bq 2597
    have hp : val WuPaper.ClassicalFourthData.Bq 2597 = (188853690335319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2597 = 188853690335319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2597 = (10597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2598) ≤ val WuPaper.ClassicalFourthData.Bq 2598
    have hp : val WuPaper.ClassicalFourthData.Bq 2598 = (188893078575769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2598 = 188893078575769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2598 = (5299:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2599) ≤ val WuPaper.ClassicalFourthData.Bq 2599
    have hp : val WuPaper.ClassicalFourthData.Bq 2599 = (188932450714745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2599 = 188932450714745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2599 = (10599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2599
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2600) ≤ val WuPaper.ClassicalFourthData.Bq 2600
    have hp : val WuPaper.ClassicalFourthData.Bq 2600 = (188971806759430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2600 = 188971806759430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2600 = (53:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2601) ≤ val WuPaper.ClassicalFourthData.Bq 2601
    have hp : val WuPaper.ClassicalFourthData.Bq 2601 = (189011146717006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2601 = 189011146717006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2601 = (10601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2602) ≤ val WuPaper.ClassicalFourthData.Bq 2602
    have hp : val WuPaper.ClassicalFourthData.Bq 2602 = (189050470594647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2602 = 189050470594647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2602 = (5301:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2603) ≤ val WuPaper.ClassicalFourthData.Bq 2603
    have hp : val WuPaper.ClassicalFourthData.Bq 2603 = (189089778399527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2603 = 189089778399527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2603 = (10603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2604) ≤ val WuPaper.ClassicalFourthData.Bq 2604
    have hp : val WuPaper.ClassicalFourthData.Bq 2604 = (189129070138813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2604 = 189129070138813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2604 = (2651:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2605) ≤ val WuPaper.ClassicalFourthData.Bq 2605
    have hp : val WuPaper.ClassicalFourthData.Bq 2605 = (189168345819670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2605 = 189168345819670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2605 = (2121:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2606) ≤ val WuPaper.ClassicalFourthData.Bq 2606
    have hp : val WuPaper.ClassicalFourthData.Bq 2606 = (189207605449258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2606 = 189207605449258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2606 = (5303:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2607) ≤ val WuPaper.ClassicalFourthData.Bq 2607
    have hp : val WuPaper.ClassicalFourthData.Bq 2607 = (189246849034735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2607 = 189246849034735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2607 = (10607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_162
