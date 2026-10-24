import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints242
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_242 (j : Fin 16) (hj : 16*242+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*242+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*242+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3872) ≤ val WuPaper.ClassicalFourthData.Bq 3872
    have hp : val WuPaper.ClassicalFourthData.Bq 3872 = (228105727301234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3872 = 228105727301234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3872 = (371:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3873) ≤ val WuPaper.ClassicalFourthData.Bq 3873
    have hp : val WuPaper.ClassicalFourthData.Bq 3873 = (228129309553589:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3873 = 228129309553589 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3873 = (11873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3874) ≤ val WuPaper.ClassicalFourthData.Bq 3874
    have hp : val WuPaper.ClassicalFourthData.Bq 3874 = (228152882399076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3874 = 228152882399076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3874 = (5937:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3875) ≤ val WuPaper.ClassicalFourthData.Bq 3875
    have hp : val WuPaper.ClassicalFourthData.Bq 3875 = (228176445841451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3875 = 228176445841451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3875 = (95:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3876) ≤ val WuPaper.ClassicalFourthData.Bq 3876
    have hp : val WuPaper.ClassicalFourthData.Bq 3876 = (228199999884470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3876 = 228199999884470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3876 = (2969:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3877) ≤ val WuPaper.ClassicalFourthData.Bq 3877
    have hp : val WuPaper.ClassicalFourthData.Bq 3877 = (228223544531885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3877 = 228223544531885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3877 = (11877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3878) ≤ val WuPaper.ClassicalFourthData.Bq 3878
    have hp : val WuPaper.ClassicalFourthData.Bq 3878 = (228247079787447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3878 = 228247079787447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3878 = (5939:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3879) ≤ val WuPaper.ClassicalFourthData.Bq 3879
    have hp : val WuPaper.ClassicalFourthData.Bq 3879 = (228270605654908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3879 = 228270605654908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3879 = (11879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3879
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3880) ≤ val WuPaper.ClassicalFourthData.Bq 3880
    have hp : val WuPaper.ClassicalFourthData.Bq 3880 = (228294122138013:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3880 = 228294122138013 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3880 = (297:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3881) ≤ val WuPaper.ClassicalFourthData.Bq 3881
    have hp : val WuPaper.ClassicalFourthData.Bq 3881 = (228317629240510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3881 = 228317629240510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3881 = (11881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3882) ≤ val WuPaper.ClassicalFourthData.Bq 3882
    have hp : val WuPaper.ClassicalFourthData.Bq 3882 = (228341126966141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3882 = 228341126966141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3882 = (5941:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3883) ≤ val WuPaper.ClassicalFourthData.Bq 3883
    have hp : val WuPaper.ClassicalFourthData.Bq 3883 = (228364615318651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3883 = 228364615318651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3883 = (11883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3884) ≤ val WuPaper.ClassicalFourthData.Bq 3884
    have hp : val WuPaper.ClassicalFourthData.Bq 3884 = (228388094301779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3884 = 228388094301779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3884 = (2971:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3885) ≤ val WuPaper.ClassicalFourthData.Bq 3885
    have hp : val WuPaper.ClassicalFourthData.Bq 3885 = (228411563919264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3885 = 228411563919264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3885 = (2377:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3886) ≤ val WuPaper.ClassicalFourthData.Bq 3886
    have hp : val WuPaper.ClassicalFourthData.Bq 3886 = (228435024174843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3886 = 228435024174843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3886 = (5943:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3887) ≤ val WuPaper.ClassicalFourthData.Bq 3887
    have hp : val WuPaper.ClassicalFourthData.Bq 3887 = (228458475072252:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3887 = 228458475072252 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3887 = (11887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_242
