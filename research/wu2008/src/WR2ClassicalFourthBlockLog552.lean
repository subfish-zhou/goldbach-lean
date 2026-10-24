import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints552
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_552 (j : Fin 16) (hj : 16*552+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*552+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*552+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8832) ≤ val WuPaper.ClassicalFourthData.Bq 8832
    have hp : val WuPaper.ClassicalFourthData.Bq 8832 = (277007530897672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8832 = 277007530897672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8832 = (526:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8833) ≤ val WuPaper.ClassicalFourthData.Bq 8833
    have hp : val WuPaper.ClassicalFourthData.Bq 8833 = (277009592385337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8833 = 277009592385337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8833 = (16833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8834) ≤ val WuPaper.ClassicalFourthData.Bq 8834
    have hp : val WuPaper.ClassicalFourthData.Bq 8834 = (277011652185248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8834 = 277011652185248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8834 = (8417:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8835) ≤ val WuPaper.ClassicalFourthData.Bq 8835
    have hp : val WuPaper.ClassicalFourthData.Bq 8835 = (277013710297932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8835 = 277013710297932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8835 = (3367:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8836) ≤ val WuPaper.ClassicalFourthData.Bq 8836
    have hp : val WuPaper.ClassicalFourthData.Bq 8836 = (277015766723914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8836 = 277015766723914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8836 = (4209:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8837) ≤ val WuPaper.ClassicalFourthData.Bq 8837
    have hp : val WuPaper.ClassicalFourthData.Bq 8837 = (277017821463719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8837 = 277017821463719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8837 = (16837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8838) ≤ val WuPaper.ClassicalFourthData.Bq 8838
    have hp : val WuPaper.ClassicalFourthData.Bq 8838 = (277019874517871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8838 = 277019874517871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8838 = (8419:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8839) ≤ val WuPaper.ClassicalFourthData.Bq 8839
    have hp : val WuPaper.ClassicalFourthData.Bq 8839 = (277021925886897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8839 = 277021925886897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8839 = (16839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8839
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8840) ≤ val WuPaper.ClassicalFourthData.Bq 8840
    have hp : val WuPaper.ClassicalFourthData.Bq 8840 = (277023975571320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8840 = 277023975571320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8840 = (421:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8841) ≤ val WuPaper.ClassicalFourthData.Bq 8841
    have hp : val WuPaper.ClassicalFourthData.Bq 8841 = (277026023571665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8841 = 277026023571665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8841 = (16841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8842) ≤ val WuPaper.ClassicalFourthData.Bq 8842
    have hp : val WuPaper.ClassicalFourthData.Bq 8842 = (277028069888457:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8842 = 277028069888457 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8842 = (8421:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8843) ≤ val WuPaper.ClassicalFourthData.Bq 8843
    have hp : val WuPaper.ClassicalFourthData.Bq 8843 = (277030114522219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8843 = 277030114522219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8843 = (16843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8844) ≤ val WuPaper.ClassicalFourthData.Bq 8844
    have hp : val WuPaper.ClassicalFourthData.Bq 8844 = (277032157473476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8844 = 277032157473476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8844 = (4211:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8845) ≤ val WuPaper.ClassicalFourthData.Bq 8845
    have hp : val WuPaper.ClassicalFourthData.Bq 8845 = (277034198742751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8845 = 277034198742751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8845 = (3369:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8846) ≤ val WuPaper.ClassicalFourthData.Bq 8846
    have hp : val WuPaper.ClassicalFourthData.Bq 8846 = (277036238330569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8846 = 277036238330569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8846 = (8423:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8847) ≤ val WuPaper.ClassicalFourthData.Bq 8847
    have hp : val WuPaper.ClassicalFourthData.Bq 8847 = (277038276237452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8847 = 277038276237452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8847 = (16847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_552
