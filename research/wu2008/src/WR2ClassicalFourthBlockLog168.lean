import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints168
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_168 (j : Fin 16) (hj : 16*168+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*168+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*168+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2688) ≤ val WuPaper.ClassicalFourthData.Bq 2688
    have hp : val WuPaper.ClassicalFourthData.Bq 2688 = (192372947104233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2688 = 192372947104233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2688 = (334:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2689) ≤ val WuPaper.ClassicalFourthData.Bq 2689
    have hp : val WuPaper.ClassicalFourthData.Bq 2689 = (192410899061234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2689 = 192410899061234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2689 = (10689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2690) ≤ val WuPaper.ClassicalFourthData.Bq 2690
    have hp : val WuPaper.ClassicalFourthData.Bq 2690 = (192448835554817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2690 = 192448835554817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2690 = (1069:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2691) ≤ val WuPaper.ClassicalFourthData.Bq 2691
    have hp : val WuPaper.ClassicalFourthData.Bq 2691 = (192486756591821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2691 = 192486756591821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2691 = (10691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2692) ≤ val WuPaper.ClassicalFourthData.Bq 2692
    have hp : val WuPaper.ClassicalFourthData.Bq 2692 = (192524662179083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2692 = 192524662179083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2692 = (2673:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2693) ≤ val WuPaper.ClassicalFourthData.Bq 2693
    have hp : val WuPaper.ClassicalFourthData.Bq 2693 = (192562552323432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2693 = 192562552323432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2693 = (10693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2694) ≤ val WuPaper.ClassicalFourthData.Bq 2694
    have hp : val WuPaper.ClassicalFourthData.Bq 2694 = (192600427031698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2694 = 192600427031698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2694 = (5347:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2695) ≤ val WuPaper.ClassicalFourthData.Bq 2695
    have hp : val WuPaper.ClassicalFourthData.Bq 2695 = (192638286310705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2695 = 192638286310705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2695 = (2139:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2695
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2696) ≤ val WuPaper.ClassicalFourthData.Bq 2696
    have hp : val WuPaper.ClassicalFourthData.Bq 2696 = (192676130167272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2696 = 192676130167272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2696 = (1337:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2697) ≤ val WuPaper.ClassicalFourthData.Bq 2697
    have hp : val WuPaper.ClassicalFourthData.Bq 2697 = (192713958608217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2697 = 192713958608217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2697 = (10697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2698) ≤ val WuPaper.ClassicalFourthData.Bq 2698
    have hp : val WuPaper.ClassicalFourthData.Bq 2698 = (192751771640353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2698 = 192751771640353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2698 = (5349:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2699) ≤ val WuPaper.ClassicalFourthData.Bq 2699
    have hp : val WuPaper.ClassicalFourthData.Bq 2699 = (192789569270489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2699 = 192789569270489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2699 = (10699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2700) ≤ val WuPaper.ClassicalFourthData.Bq 2700
    have hp : val WuPaper.ClassicalFourthData.Bq 2700 = (192827351505432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2700 = 192827351505432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2700 = (107:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2701) ≤ val WuPaper.ClassicalFourthData.Bq 2701
    have hp : val WuPaper.ClassicalFourthData.Bq 2701 = (192865118351984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2701 = 192865118351984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2701 = (10701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2702) ≤ val WuPaper.ClassicalFourthData.Bq 2702
    have hp : val WuPaper.ClassicalFourthData.Bq 2702 = (192902869816942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2702 = 192902869816942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2702 = (5351:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2703) ≤ val WuPaper.ClassicalFourthData.Bq 2703
    have hp : val WuPaper.ClassicalFourthData.Bq 2703 = (192940605907103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2703 = 192940605907103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2703 = (10703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_168
