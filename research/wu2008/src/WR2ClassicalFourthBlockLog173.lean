import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints173
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_173 (j : Fin 16) (hj : 16*173+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*173+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*173+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2768) ≤ val WuPaper.ClassicalFourthData.Bq 2768
    have hp : val WuPaper.ClassicalFourthData.Bq 2768 = (195360795387828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2768 = 195360795387828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2768 = (673:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2769) ≤ val WuPaper.ClassicalFourthData.Bq 2769
    have hp : val WuPaper.ClassicalFourthData.Bq 2769 = (195397531583836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2769 = 195397531583836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2769 = (10769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2770) ≤ val WuPaper.ClassicalFourthData.Bq 2770
    have hp : val WuPaper.ClassicalFourthData.Bq 2770 = (195434252852106:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2770 = 195434252852106 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2770 = (1077:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2771) ≤ val WuPaper.ClassicalFourthData.Bq 2771
    have hp : val WuPaper.ClassicalFourthData.Bq 2771 = (195470959199190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2771 = 195470959199190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2771 = (10771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2772) ≤ val WuPaper.ClassicalFourthData.Bq 2772
    have hp : val WuPaper.ClassicalFourthData.Bq 2772 = (195507650631637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2772 = 195507650631637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2772 = (2693:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2773) ≤ val WuPaper.ClassicalFourthData.Bq 2773
    have hp : val WuPaper.ClassicalFourthData.Bq 2773 = (195544327155993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2773 = 195544327155993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2773 = (10773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2774) ≤ val WuPaper.ClassicalFourthData.Bq 2774
    have hp : val WuPaper.ClassicalFourthData.Bq 2774 = (195580988778797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2774 = 195580988778797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2774 = (5387:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2775) ≤ val WuPaper.ClassicalFourthData.Bq 2775
    have hp : val WuPaper.ClassicalFourthData.Bq 2775 = (195617635506589:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2775 = 195617635506589 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2775 = (431:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2775
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2776) ≤ val WuPaper.ClassicalFourthData.Bq 2776
    have hp : val WuPaper.ClassicalFourthData.Bq 2776 = (195654267345903:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2776 = 195654267345903 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2776 = (1347:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2777) ≤ val WuPaper.ClassicalFourthData.Bq 2777
    have hp : val WuPaper.ClassicalFourthData.Bq 2777 = (195690884303271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2777 = 195690884303271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2777 = (10777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2778) ≤ val WuPaper.ClassicalFourthData.Bq 2778
    have hp : val WuPaper.ClassicalFourthData.Bq 2778 = (195727486385218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2778 = 195727486385218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2778 = (5389:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2779) ≤ val WuPaper.ClassicalFourthData.Bq 2779
    have hp : val WuPaper.ClassicalFourthData.Bq 2779 = (195764073598270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2779 = 195764073598270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2779 = (10779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2780) ≤ val WuPaper.ClassicalFourthData.Bq 2780
    have hp : val WuPaper.ClassicalFourthData.Bq 2780 = (195800645948948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2780 = 195800645948948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2780 = (539:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2781) ≤ val WuPaper.ClassicalFourthData.Bq 2781
    have hp : val WuPaper.ClassicalFourthData.Bq 2781 = (195837203443768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2781 = 195837203443768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2781 = (10781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2782) ≤ val WuPaper.ClassicalFourthData.Bq 2782
    have hp : val WuPaper.ClassicalFourthData.Bq 2782 = (195873746089244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2782 = 195873746089244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2782 = (5391:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2783) ≤ val WuPaper.ClassicalFourthData.Bq 2783
    have hp : val WuPaper.ClassicalFourthData.Bq 2783 = (195910273891887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2783 = 195910273891887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2783 = (10783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_173
