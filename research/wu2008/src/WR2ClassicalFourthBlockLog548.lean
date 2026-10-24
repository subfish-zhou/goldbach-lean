import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints548
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_548 (j : Fin 16) (hj : 16*548+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*548+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*548+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8768) ≤ val WuPaper.ClassicalFourthData.Bq 8768
    have hp : val WuPaper.ClassicalFourthData.Bq 8768 = (276872060973099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8768 = 276872060973099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8768 = (524:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8769) ≤ val WuPaper.ClassicalFourthData.Bq 8769
    have hp : val WuPaper.ClassicalFourthData.Bq 8769 = (276874231578351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8769 = 276874231578351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8769 = (16769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8770) ≤ val WuPaper.ClassicalFourthData.Bq 8770
    have hp : val WuPaper.ClassicalFourthData.Bq 8770 = (276876400461841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8770 = 276876400461841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8770 = (1677:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8771) ≤ val WuPaper.ClassicalFourthData.Bq 8771
    have hp : val WuPaper.ClassicalFourthData.Bq 8771 = (276878567624105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8771 = 276878567624105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8771 = (16771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8772) ≤ val WuPaper.ClassicalFourthData.Bq 8772
    have hp : val WuPaper.ClassicalFourthData.Bq 8772 = (276880733065681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8772 = 276880733065681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8772 = (4193:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8773) ≤ val WuPaper.ClassicalFourthData.Bq 8773
    have hp : val WuPaper.ClassicalFourthData.Bq 8773 = (276882896787104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8773 = 276882896787104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8773 = (16773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8774) ≤ val WuPaper.ClassicalFourthData.Bq 8774
    have hp : val WuPaper.ClassicalFourthData.Bq 8774 = (276885058788913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8774 = 276885058788913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8774 = (8387:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8775) ≤ val WuPaper.ClassicalFourthData.Bq 8775
    have hp : val WuPaper.ClassicalFourthData.Bq 8775 = (276887219071642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8775 = 276887219071642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8775 = (671:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8775
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8776) ≤ val WuPaper.ClassicalFourthData.Bq 8776
    have hp : val WuPaper.ClassicalFourthData.Bq 8776 = (276889377635828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8776 = 276889377635828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8776 = (2097:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8777) ≤ val WuPaper.ClassicalFourthData.Bq 8777
    have hp : val WuPaper.ClassicalFourthData.Bq 8777 = (276891534482007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8777 = 276891534482007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8777 = (16777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8778) ≤ val WuPaper.ClassicalFourthData.Bq 8778
    have hp : val WuPaper.ClassicalFourthData.Bq 8778 = (276893689610716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8778 = 276893689610716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8778 = (8389:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8779) ≤ val WuPaper.ClassicalFourthData.Bq 8779
    have hp : val WuPaper.ClassicalFourthData.Bq 8779 = (276895843022489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8779 = 276895843022489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8779 = (16779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8780) ≤ val WuPaper.ClassicalFourthData.Bq 8780
    have hp : val WuPaper.ClassicalFourthData.Bq 8780 = (276897994717861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8780 = 276897994717861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8780 = (839:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8781) ≤ val WuPaper.ClassicalFourthData.Bq 8781
    have hp : val WuPaper.ClassicalFourthData.Bq 8781 = (276900144697369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8781 = 276900144697369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8781 = (16781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8782) ≤ val WuPaper.ClassicalFourthData.Bq 8782
    have hp : val WuPaper.ClassicalFourthData.Bq 8782 = (276902292961548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8782 = 276902292961548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8782 = (8391:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8783) ≤ val WuPaper.ClassicalFourthData.Bq 8783
    have hp : val WuPaper.ClassicalFourthData.Bq 8783 = (276904439510932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8783 = 276904439510932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8783 = (16783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_548
