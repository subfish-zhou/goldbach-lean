import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints564
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_564 (j : Fin 16) (hj : 16*564+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*564+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*564+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9024) ≤ val WuPaper.ClassicalFourthData.Bq 9024
    have hp : val WuPaper.ClassicalFourthData.Bq 9024 = (277372990638844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9024 = 277372990638844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9024 = (532:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9025) ≤ val WuPaper.ClassicalFourthData.Bq 9025
    have hp : val WuPaper.ClassicalFourthData.Bq 9025 = (277374737512646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9025 = 277374737512646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9025 = (681:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9026) ≤ val WuPaper.ClassicalFourthData.Bq 9026
    have hp : val WuPaper.ClassicalFourthData.Bq 9026 = (277376482796432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9026 = 277376482796432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9026 = (8513:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9027) ≤ val WuPaper.ClassicalFourthData.Bq 9027
    have hp : val WuPaper.ClassicalFourthData.Bq 9027 = (277378226490694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9027 = 277378226490694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9027 = (17027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9028) ≤ val WuPaper.ClassicalFourthData.Bq 9028
    have hp : val WuPaper.ClassicalFourthData.Bq 9028 = (277379968595926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9028 = 277379968595926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9028 = (4257:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9029) ≤ val WuPaper.ClassicalFourthData.Bq 9029
    have hp : val WuPaper.ClassicalFourthData.Bq 9029 = (277381709112619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9029 = 277381709112619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9029 = (17029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9030) ≤ val WuPaper.ClassicalFourthData.Bq 9030
    have hp : val WuPaper.ClassicalFourthData.Bq 9030 = (277383448041266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9030 = 277383448041266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9030 = (1703:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9031) ≤ val WuPaper.ClassicalFourthData.Bq 9031
    have hp : val WuPaper.ClassicalFourthData.Bq 9031 = (277385185382359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9031 = 277385185382359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9031 = (17031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9031
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9032) ≤ val WuPaper.ClassicalFourthData.Bq 9032
    have hp : val WuPaper.ClassicalFourthData.Bq 9032 = (277386921136390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9032 = 277386921136390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9032 = (2129:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9033) ≤ val WuPaper.ClassicalFourthData.Bq 9033
    have hp : val WuPaper.ClassicalFourthData.Bq 9033 = (277388655303850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9033 = 277388655303850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9033 = (17033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9034) ≤ val WuPaper.ClassicalFourthData.Bq 9034
    have hp : val WuPaper.ClassicalFourthData.Bq 9034 = (277390387885232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9034 = 277390387885232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9034 = (8517:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9035) ≤ val WuPaper.ClassicalFourthData.Bq 9035
    have hp : val WuPaper.ClassicalFourthData.Bq 9035 = (277392118881026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9035 = 277392118881026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9035 = (3407:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9036) ≤ val WuPaper.ClassicalFourthData.Bq 9036
    have hp : val WuPaper.ClassicalFourthData.Bq 9036 = (277393848291724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9036 = 277393848291724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9036 = (4259:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9037) ≤ val WuPaper.ClassicalFourthData.Bq 9037
    have hp : val WuPaper.ClassicalFourthData.Bq 9037 = (277395576117818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9037 = 277395576117818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9037 = (17037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9038) ≤ val WuPaper.ClassicalFourthData.Bq 9038
    have hp : val WuPaper.ClassicalFourthData.Bq 9038 = (277397302359797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9038 = 277397302359797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9038 = (8519:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9039) ≤ val WuPaper.ClassicalFourthData.Bq 9039
    have hp : val WuPaper.ClassicalFourthData.Bq 9039 = (277399027018153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9039 = 277399027018153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9039 = (17039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_564
