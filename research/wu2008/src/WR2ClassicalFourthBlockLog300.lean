import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints300
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_300 (j : Fin 16) (hj : 16*300+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*300+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*300+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4800) ≤ val WuPaper.ClassicalFourthData.Bq 4800
    have hp : val WuPaper.ClassicalFourthData.Bq 4800 = (246392925113835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4800 = 246392925113835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4800 = (16:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4801) ≤ val WuPaper.ClassicalFourthData.Bq 4801
    have hp : val WuPaper.ClassicalFourthData.Bq 4801 = (246409183742453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4801 = 246409183742453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4801 = (12801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4802) ≤ val WuPaper.ClassicalFourthData.Bq 4802
    have hp : val WuPaper.ClassicalFourthData.Bq 4802 = (246425435797223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4802 = 246425435797223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4802 = (6401:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4803) ≤ val WuPaper.ClassicalFourthData.Bq 4803
    have hp : val WuPaper.ClassicalFourthData.Bq 4803 = (246441681280600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4803 = 246441681280600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4803 = (12803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4804) ≤ val WuPaper.ClassicalFourthData.Bq 4804
    have hp : val WuPaper.ClassicalFourthData.Bq 4804 = (246457920195041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4804 = 246457920195041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4804 = (3201:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4805) ≤ val WuPaper.ClassicalFourthData.Bq 4805
    have hp : val WuPaper.ClassicalFourthData.Bq 4805 = (246474152543001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4805 = 246474152543001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4805 = (2561:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4806) ≤ val WuPaper.ClassicalFourthData.Bq 4806
    have hp : val WuPaper.ClassicalFourthData.Bq 4806 = (246490378326932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4806 = 246490378326932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4806 = (6403:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4807) ≤ val WuPaper.ClassicalFourthData.Bq 4807
    have hp : val WuPaper.ClassicalFourthData.Bq 4807 = (246506597549288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4807 = 246506597549288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4807 = (12807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4807
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4808) ≤ val WuPaper.ClassicalFourthData.Bq 4808
    have hp : val WuPaper.ClassicalFourthData.Bq 4808 = (246522810212520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4808 = 246522810212520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4808 = (1601:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4809) ≤ val WuPaper.ClassicalFourthData.Bq 4809
    have hp : val WuPaper.ClassicalFourthData.Bq 4809 = (246539016319079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4809 = 246539016319079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4809 = (12809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4810) ≤ val WuPaper.ClassicalFourthData.Bq 4810
    have hp : val WuPaper.ClassicalFourthData.Bq 4810 = (246555215871413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4810 = 246555215871413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4810 = (1281:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4811) ≤ val WuPaper.ClassicalFourthData.Bq 4811
    have hp : val WuPaper.ClassicalFourthData.Bq 4811 = (246571408871971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4811 = 246571408871971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4811 = (12811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4812) ≤ val WuPaper.ClassicalFourthData.Bq 4812
    have hp : val WuPaper.ClassicalFourthData.Bq 4812 = (246587595323199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4812 = 246587595323199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4812 = (3203:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4813) ≤ val WuPaper.ClassicalFourthData.Bq 4813
    have hp : val WuPaper.ClassicalFourthData.Bq 4813 = (246603775227545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4813 = 246603775227545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4813 = (12813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4814) ≤ val WuPaper.ClassicalFourthData.Bq 4814
    have hp : val WuPaper.ClassicalFourthData.Bq 4814 = (246619948587453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4814 = 246619948587453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4814 = (6407:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4815) ≤ val WuPaper.ClassicalFourthData.Bq 4815
    have hp : val WuPaper.ClassicalFourthData.Bq 4815 = (246636115405367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4815 = 246636115405367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4815 = (2563:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_300
