import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints501
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_501 (j : Fin 16) (hj : 16*501+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*501+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*501+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8016) ≤ val WuPaper.ClassicalFourthData.Bq 8016
    have hp : val WuPaper.ClassicalFourthData.Bq 8016 = (274711472004128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8016 = 274711472004128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8016 = (1001:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8017) ≤ val WuPaper.ClassicalFourthData.Bq 8017
    have hp : val WuPaper.ClassicalFourthData.Bq 8017 = (274715103405611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8017 = 274715103405611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8017 = (16017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8018) ≤ val WuPaper.ClassicalFourthData.Bq 8018
    have hp : val WuPaper.ClassicalFourthData.Bq 8018 = (274718732624422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8018 = 274718732624422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8018 = (8009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8019) ≤ val WuPaper.ClassicalFourthData.Bq 8019
    have hp : val WuPaper.ClassicalFourthData.Bq 8019 = (274722359661257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8019 = 274722359661257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8019 = (16019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8020) ≤ val WuPaper.ClassicalFourthData.Bq 8020
    have hp : val WuPaper.ClassicalFourthData.Bq 8020 = (274725984516812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8020 = 274725984516812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8020 = (801:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8021) ≤ val WuPaper.ClassicalFourthData.Bq 8021
    have hp : val WuPaper.ClassicalFourthData.Bq 8021 = (274729607191784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8021 = 274729607191784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8021 = (16021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8022) ≤ val WuPaper.ClassicalFourthData.Bq 8022
    have hp : val WuPaper.ClassicalFourthData.Bq 8022 = (274733227686869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8022 = 274733227686869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8022 = (8011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8023) ≤ val WuPaper.ClassicalFourthData.Bq 8023
    have hp : val WuPaper.ClassicalFourthData.Bq 8023 = (274736846002761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8023 = 274736846002761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8023 = (16023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8023
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8024) ≤ val WuPaper.ClassicalFourthData.Bq 8024
    have hp : val WuPaper.ClassicalFourthData.Bq 8024 = (274740462140156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8024 = 274740462140156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8024 = (2003:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8025) ≤ val WuPaper.ClassicalFourthData.Bq 8025
    have hp : val WuPaper.ClassicalFourthData.Bq 8025 = (274744076099750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8025 = 274744076099750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8025 = (641:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8026) ≤ val WuPaper.ClassicalFourthData.Bq 8026
    have hp : val WuPaper.ClassicalFourthData.Bq 8026 = (274747687882237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8026 = 274747687882237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8026 = (8013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8027) ≤ val WuPaper.ClassicalFourthData.Bq 8027
    have hp : val WuPaper.ClassicalFourthData.Bq 8027 = (274751297488311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8027 = 274751297488311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8027 = (16027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8028) ≤ val WuPaper.ClassicalFourthData.Bq 8028
    have hp : val WuPaper.ClassicalFourthData.Bq 8028 = (274754904918667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8028 = 274754904918667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8028 = (4007:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8029) ≤ val WuPaper.ClassicalFourthData.Bq 8029
    have hp : val WuPaper.ClassicalFourthData.Bq 8029 = (274758510173999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8029 = 274758510173999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8029 = (16029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8030) ≤ val WuPaper.ClassicalFourthData.Bq 8030
    have hp : val WuPaper.ClassicalFourthData.Bq 8030 = (274762113255001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8030 = 274762113255001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8030 = (1603:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8031) ≤ val WuPaper.ClassicalFourthData.Bq 8031
    have hp : val WuPaper.ClassicalFourthData.Bq 8031 = (274765714162366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8031 = 274765714162366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8031 = (16031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_501
