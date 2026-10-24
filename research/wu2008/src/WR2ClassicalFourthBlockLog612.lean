import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints612
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_612 (j : Fin 16) (hj : 16*612+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*612+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*612+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9792) ≤ val WuPaper.ClassicalFourthData.Bq 9792
    have hp : val WuPaper.ClassicalFourthData.Bq 9792 = (278281104512132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9792 = 278281104512132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9792 = (556:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9793) ≤ val WuPaper.ClassicalFourthData.Bq 9793
    have hp : val WuPaper.ClassicalFourthData.Bq 9793 = (278281763849181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9793 = 278281763849181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9793 = (17793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9794) ≤ val WuPaper.ClassicalFourthData.Bq 9794
    have hp : val WuPaper.ClassicalFourthData.Bq 9794 = (278282421930526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9794 = 278282421930526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9794 = (8897:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9795) ≤ val WuPaper.ClassicalFourthData.Bq 9795
    have hp : val WuPaper.ClassicalFourthData.Bq 9795 = (278283078756551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9795 = 278283078756551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9795 = (3559:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9796) ≤ val WuPaper.ClassicalFourthData.Bq 9796
    have hp : val WuPaper.ClassicalFourthData.Bq 9796 = (278283734327638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9796 = 278283734327638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9796 = (4449:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9797) ≤ val WuPaper.ClassicalFourthData.Bq 9797
    have hp : val WuPaper.ClassicalFourthData.Bq 9797 = (278284388644170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9797 = 278284388644170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9797 = (17797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9798) ≤ val WuPaper.ClassicalFourthData.Bq 9798
    have hp : val WuPaper.ClassicalFourthData.Bq 9798 = (278285041706530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9798 = 278285041706530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9798 = (8899:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9799) ≤ val WuPaper.ClassicalFourthData.Bq 9799
    have hp : val WuPaper.ClassicalFourthData.Bq 9799 = (278285693515100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9799 = 278285693515100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9799 = (17799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9799
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9800) ≤ val WuPaper.ClassicalFourthData.Bq 9800
    have hp : val WuPaper.ClassicalFourthData.Bq 9800 = (278286344070263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9800 = 278286344070263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9800 = (89:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9801) ≤ val WuPaper.ClassicalFourthData.Bq 9801
    have hp : val WuPaper.ClassicalFourthData.Bq 9801 = (278286993372400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9801 = 278286993372400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9801 = (17801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9802) ≤ val WuPaper.ClassicalFourthData.Bq 9802
    have hp : val WuPaper.ClassicalFourthData.Bq 9802 = (278287641421895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9802 = 278287641421895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9802 = (8901:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9803) ≤ val WuPaper.ClassicalFourthData.Bq 9803
    have hp : val WuPaper.ClassicalFourthData.Bq 9803 = (278288288219128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9803 = 278288288219128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9803 = (17803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9804) ≤ val WuPaper.ClassicalFourthData.Bq 9804
    have hp : val WuPaper.ClassicalFourthData.Bq 9804 = (278288933764483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9804 = 278288933764483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9804 = (4451:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9805) ≤ val WuPaper.ClassicalFourthData.Bq 9805
    have hp : val WuPaper.ClassicalFourthData.Bq 9805 = (278289578058340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9805 = 278289578058340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9805 = (3561:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9806) ≤ val WuPaper.ClassicalFourthData.Bq 9806
    have hp : val WuPaper.ClassicalFourthData.Bq 9806 = (278290221101082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9806 = 278290221101082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9806 = (8903:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9807) ≤ val WuPaper.ClassicalFourthData.Bq 9807
    have hp : val WuPaper.ClassicalFourthData.Bq 9807 = (278290862893089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9807 = 278290862893089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9807 = (17807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_612
