import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints614
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_614 (j : Fin 16) (hj : 16*614+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*614+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*614+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9824) ≤ val WuPaper.ClassicalFourthData.Bq 9824
    have hp : val WuPaper.ClassicalFourthData.Bq 9824 = (278301582363987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9824 = 278301582363987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9824 = (557:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9825) ≤ val WuPaper.ClassicalFourthData.Bq 9825
    have hp : val WuPaper.ClassicalFourthData.Bq 9825 = (278302201707880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9825 = 278302201707880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9825 = (713:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9826) ≤ val WuPaper.ClassicalFourthData.Bq 9826
    have hp : val WuPaper.ClassicalFourthData.Bq 9826 = (278302819808265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9826 = 278302819808265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9826 = (8913:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9827) ≤ val WuPaper.ClassicalFourthData.Bq 9827
    have hp : val WuPaper.ClassicalFourthData.Bq 9827 = (278303436665520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9827 = 278303436665520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9827 = (17827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9828) ≤ val WuPaper.ClassicalFourthData.Bq 9828
    have hp : val WuPaper.ClassicalFourthData.Bq 9828 = (278304052280024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9828 = 278304052280024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9828 = (4457:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9829) ≤ val WuPaper.ClassicalFourthData.Bq 9829
    have hp : val WuPaper.ClassicalFourthData.Bq 9829 = (278304666652157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9829 = 278304666652157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9829 = (17829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9830) ≤ val WuPaper.ClassicalFourthData.Bq 9830
    have hp : val WuPaper.ClassicalFourthData.Bq 9830 = (278305279782297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9830 = 278305279782297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9830 = (1783:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9831) ≤ val WuPaper.ClassicalFourthData.Bq 9831
    have hp : val WuPaper.ClassicalFourthData.Bq 9831 = (278305891670823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9831 = 278305891670823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9831 = (17831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9831
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9832) ≤ val WuPaper.ClassicalFourthData.Bq 9832
    have hp : val WuPaper.ClassicalFourthData.Bq 9832 = (278306502318112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9832 = 278306502318112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9832 = (2229:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9833) ≤ val WuPaper.ClassicalFourthData.Bq 9833
    have hp : val WuPaper.ClassicalFourthData.Bq 9833 = (278307111724545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9833 = 278307111724545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9833 = (17833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9834) ≤ val WuPaper.ClassicalFourthData.Bq 9834
    have hp : val WuPaper.ClassicalFourthData.Bq 9834 = (278307719890497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9834 = 278307719890497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9834 = (8917:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9835) ≤ val WuPaper.ClassicalFourthData.Bq 9835
    have hp : val WuPaper.ClassicalFourthData.Bq 9835 = (278308326816349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9835 = 278308326816349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9835 = (3567:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9836) ≤ val WuPaper.ClassicalFourthData.Bq 9836
    have hp : val WuPaper.ClassicalFourthData.Bq 9836 = (278308932502477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9836 = 278308932502477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9836 = (4459:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9837) ≤ val WuPaper.ClassicalFourthData.Bq 9837
    have hp : val WuPaper.ClassicalFourthData.Bq 9837 = (278309536949260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9837 = 278309536949260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9837 = (17837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9838) ≤ val WuPaper.ClassicalFourthData.Bq 9838
    have hp : val WuPaper.ClassicalFourthData.Bq 9838 = (278310140157075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9838 = 278310140157075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9838 = (8919:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9839) ≤ val WuPaper.ClassicalFourthData.Bq 9839
    have hp : val WuPaper.ClassicalFourthData.Bq 9839 = (278310742126301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9839 = 278310742126301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9839 = (17839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_614
