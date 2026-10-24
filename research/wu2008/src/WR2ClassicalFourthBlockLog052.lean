import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints052
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_052 (j : Fin 16) (hj : 16*52+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*52+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*52+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 832) ≤ val WuPaper.ClassicalFourthData.Bq 832
    have hp : val WuPaper.ClassicalFourthData.Bq 832 = (85582472605355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 832 = 85582472605355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 832 = (276:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 833) ≤ val WuPaper.ClassicalFourthData.Bq 833
    have hp : val WuPaper.ClassicalFourthData.Bq 833 = (85666492355058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 833 = 85666492355058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 833 = (8833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 834) ≤ val WuPaper.ClassicalFourthData.Bq 834
    have hp : val WuPaper.ClassicalFourthData.Bq 834 = (85750473697714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 834 = 85750473697714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 834 = (4417:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 835) ≤ val WuPaper.ClassicalFourthData.Bq 835
    have hp : val WuPaper.ClassicalFourthData.Bq 835 = (85834416654383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 835 = 85834416654383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 835 = (1767:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 836) ≤ val WuPaper.ClassicalFourthData.Bq 836
    have hp : val WuPaper.ClassicalFourthData.Bq 836 = (85918321246110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 836 = 85918321246110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 836 = (2209:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 837) ≤ val WuPaper.ClassicalFourthData.Bq 837
    have hp : val WuPaper.ClassicalFourthData.Bq 837 = (86002187493926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 837 = 86002187493926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 837 = (8837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 838) ≤ val WuPaper.ClassicalFourthData.Bq 838
    have hp : val WuPaper.ClassicalFourthData.Bq 838 = (86086015418849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 838 = 86086015418849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 838 = (4419:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 839) ≤ val WuPaper.ClassicalFourthData.Bq 839
    have hp : val WuPaper.ClassicalFourthData.Bq 839 = (86169805041879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 839 = 86169805041879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 839 = (8839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_839
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 840) ≤ val WuPaper.ClassicalFourthData.Bq 840
    have hp : val WuPaper.ClassicalFourthData.Bq 840 = (86253556384005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 840 = 86253556384005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 840 = (221:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 841) ≤ val WuPaper.ClassicalFourthData.Bq 841
    have hp : val WuPaper.ClassicalFourthData.Bq 841 = (86337269466200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 841 = 86337269466200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 841 = (8841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 842) ≤ val WuPaper.ClassicalFourthData.Bq 842
    have hp : val WuPaper.ClassicalFourthData.Bq 842 = (86420944309422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 842 = 86420944309422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 842 = (4421:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 843) ≤ val WuPaper.ClassicalFourthData.Bq 843
    have hp : val WuPaper.ClassicalFourthData.Bq 843 = (86504580934616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 843 = 86504580934616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 843 = (8843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 844) ≤ val WuPaper.ClassicalFourthData.Bq 844
    have hp : val WuPaper.ClassicalFourthData.Bq 844 = (86588179362712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 844 = 86588179362712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 844 = (2211:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 845) ≤ val WuPaper.ClassicalFourthData.Bq 845
    have hp : val WuPaper.ClassicalFourthData.Bq 845 = (86671739614625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 845 = 86671739614625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 845 = (1769:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 846) ≤ val WuPaper.ClassicalFourthData.Bq 846
    have hp : val WuPaper.ClassicalFourthData.Bq 846 = (86755261711257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 846 = 86755261711257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 846 = (4423:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 847) ≤ val WuPaper.ClassicalFourthData.Bq 847
    have hp : val WuPaper.ClassicalFourthData.Bq 847 = (86838745673494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 847 = 86838745673494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 847 = (8847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_052
