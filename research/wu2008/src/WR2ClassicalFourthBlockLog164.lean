import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints164
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_164 (j : Fin 16) (hj : 16*164+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*164+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*164+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2624) ≤ val WuPaper.ClassicalFourthData.Bq 2624
    have hp : val WuPaper.ClassicalFourthData.Bq 2624 = (189911542154770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2624 = 189911542154770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2624 = (332:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2625) ≤ val WuPaper.ClassicalFourthData.Bq 2625
    have hp : val WuPaper.ClassicalFourthData.Bq 2625 = (189950498165608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2625 = 189950498165608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2625 = (85:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2626) ≤ val WuPaper.ClassicalFourthData.Bq 2626
    have hp : val WuPaper.ClassicalFourthData.Bq 2626 = (189989438267576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2626 = 189989438267576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2626 = (5313:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2627) ≤ val WuPaper.ClassicalFourthData.Bq 2627
    have hp : val WuPaper.ClassicalFourthData.Bq 2627 = (190028362467752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2627 = 190028362467752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2627 = (10627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2628) ≤ val WuPaper.ClassicalFourthData.Bq 2628
    have hp : val WuPaper.ClassicalFourthData.Bq 2628 = (190067270773213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2628 = 190067270773213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2628 = (2657:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2629) ≤ val WuPaper.ClassicalFourthData.Bq 2629
    have hp : val WuPaper.ClassicalFourthData.Bq 2629 = (190106163191030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2629 = 190106163191030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2629 = (10629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2630) ≤ val WuPaper.ClassicalFourthData.Bq 2630
    have hp : val WuPaper.ClassicalFourthData.Bq 2630 = (190145039728272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2630 = 190145039728272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2630 = (1063:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2631) ≤ val WuPaper.ClassicalFourthData.Bq 2631
    have hp : val WuPaper.ClassicalFourthData.Bq 2631 = (190183900392001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2631 = 190183900392001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2631 = (10631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2631
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2632) ≤ val WuPaper.ClassicalFourthData.Bq 2632
    have hp : val WuPaper.ClassicalFourthData.Bq 2632 = (190222745189279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2632 = 190222745189279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2632 = (1329:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2633) ≤ val WuPaper.ClassicalFourthData.Bq 2633
    have hp : val WuPaper.ClassicalFourthData.Bq 2633 = (190261574127162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2633 = 190261574127162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2633 = (10633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2634) ≤ val WuPaper.ClassicalFourthData.Bq 2634
    have hp : val WuPaper.ClassicalFourthData.Bq 2634 = (190300387212703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2634 = 190300387212703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2634 = (5317:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2635) ≤ val WuPaper.ClassicalFourthData.Bq 2635
    have hp : val WuPaper.ClassicalFourthData.Bq 2635 = (190339184452950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2635 = 190339184452950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2635 = (2127:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2636) ≤ val WuPaper.ClassicalFourthData.Bq 2636
    have hp : val WuPaper.ClassicalFourthData.Bq 2636 = (190377965854949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2636 = 190377965854949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2636 = (2659:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2637) ≤ val WuPaper.ClassicalFourthData.Bq 2637
    have hp : val WuPaper.ClassicalFourthData.Bq 2637 = (190416731425740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2637 = 190416731425740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2637 = (10637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2638) ≤ val WuPaper.ClassicalFourthData.Bq 2638
    have hp : val WuPaper.ClassicalFourthData.Bq 2638 = (190455481172361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2638 = 190455481172361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2638 = (5319:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2639) ≤ val WuPaper.ClassicalFourthData.Bq 2639
    have hp : val WuPaper.ClassicalFourthData.Bq 2639 = (190494215101845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2639 = 190494215101845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2639 = (10639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_164
