import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints171
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_171 (j : Fin 16) (hj : 16*171+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*171+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*171+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2736) ≤ val WuPaper.ClassicalFourthData.Bq 2736
    have hp : val WuPaper.ClassicalFourthData.Bq 2736 = (194177315879335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2736 = 194177315879335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2736 = (671:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2737) ≤ val WuPaper.ClassicalFourthData.Bq 2737
    have hp : val WuPaper.ClassicalFourthData.Bq 2737 = (194214533243414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2737 = 194214533243414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2737 = (10737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2738) ≤ val WuPaper.ClassicalFourthData.Bq 2738
    have hp : val WuPaper.ClassicalFourthData.Bq 2738 = (194251735468233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2738 = 194251735468233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2738 = (5369:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2739) ≤ val WuPaper.ClassicalFourthData.Bq 2739
    have hp : val WuPaper.ClassicalFourthData.Bq 2739 = (194288922560458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2739 = 194288922560458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2739 = (10739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2740) ≤ val WuPaper.ClassicalFourthData.Bq 2740
    have hp : val WuPaper.ClassicalFourthData.Bq 2740 = (194326094526751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2740 = 194326094526751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2740 = (537:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2741) ≤ val WuPaper.ClassicalFourthData.Bq 2741
    have hp : val WuPaper.ClassicalFourthData.Bq 2741 = (194363251373769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2741 = 194363251373769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2741 = (10741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2742) ≤ val WuPaper.ClassicalFourthData.Bq 2742
    have hp : val WuPaper.ClassicalFourthData.Bq 2742 = (194400393108166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2742 = 194400393108166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2742 = (5371:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2743) ≤ val WuPaper.ClassicalFourthData.Bq 2743
    have hp : val WuPaper.ClassicalFourthData.Bq 2743 = (194437519736593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2743 = 194437519736593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2743 = (10743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2743
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2744) ≤ val WuPaper.ClassicalFourthData.Bq 2744
    have hp : val WuPaper.ClassicalFourthData.Bq 2744 = (194474631265698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2744 = 194474631265698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2744 = (1343:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2745) ≤ val WuPaper.ClassicalFourthData.Bq 2745
    have hp : val WuPaper.ClassicalFourthData.Bq 2745 = (194511727702124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2745 = 194511727702124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2745 = (2149:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2746) ≤ val WuPaper.ClassicalFourthData.Bq 2746
    have hp : val WuPaper.ClassicalFourthData.Bq 2746 = (194548809052510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2746 = 194548809052510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2746 = (5373:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2747) ≤ val WuPaper.ClassicalFourthData.Bq 2747
    have hp : val WuPaper.ClassicalFourthData.Bq 2747 = (194585875323495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2747 = 194585875323495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2747 = (10747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2748) ≤ val WuPaper.ClassicalFourthData.Bq 2748
    have hp : val WuPaper.ClassicalFourthData.Bq 2748 = (194622926521709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2748 = 194622926521709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2748 = (2687:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2749) ≤ val WuPaper.ClassicalFourthData.Bq 2749
    have hp : val WuPaper.ClassicalFourthData.Bq 2749 = (194659962653784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2749 = 194659962653784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2749 = (10749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2750) ≤ val WuPaper.ClassicalFourthData.Bq 2750
    have hp : val WuPaper.ClassicalFourthData.Bq 2750 = (194696983726344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2750 = 194696983726344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2750 = (43:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2751) ≤ val WuPaper.ClassicalFourthData.Bq 2751
    have hp : val WuPaper.ClassicalFourthData.Bq 2751 = (194733989746012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2751 = 194733989746012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2751 = (10751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_171
