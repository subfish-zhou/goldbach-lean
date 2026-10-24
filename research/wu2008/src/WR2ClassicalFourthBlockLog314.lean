import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints314
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_314 (j : Fin 16) (hj : 16*314+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*314+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*314+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5024) ≤ val WuPaper.ClassicalFourthData.Bq 5024
    have hp : val WuPaper.ClassicalFourthData.Bq 5024 = (249875102468002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5024 = 249875102468002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5024 = (407:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5025) ≤ val WuPaper.ClassicalFourthData.Bq 5025
    have hp : val WuPaper.ClassicalFourthData.Bq 5025 = (249889947976678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5025 = 249889947976678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5025 = (521:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5026) ≤ val WuPaper.ClassicalFourthData.Bq 5026
    have hp : val WuPaper.ClassicalFourthData.Bq 5026 = (249904787435873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5026 = 249904787435873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5026 = (6513:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5027) ≤ val WuPaper.ClassicalFourthData.Bq 5027
    have hp : val WuPaper.ClassicalFourthData.Bq 5027 = (249919620847817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5027 = 249919620847817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5027 = (13027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5028) ≤ val WuPaper.ClassicalFourthData.Bq 5028
    have hp : val WuPaper.ClassicalFourthData.Bq 5028 = (249934448214738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5028 = 249934448214738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5028 = (3257:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5029) ≤ val WuPaper.ClassicalFourthData.Bq 5029
    have hp : val WuPaper.ClassicalFourthData.Bq 5029 = (249949269538861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5029 = 249949269538861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5029 = (13029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5030) ≤ val WuPaper.ClassicalFourthData.Bq 5030
    have hp : val WuPaper.ClassicalFourthData.Bq 5030 = (249964084822412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5030 = 249964084822412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5030 = (1303:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5031) ≤ val WuPaper.ClassicalFourthData.Bq 5031
    have hp : val WuPaper.ClassicalFourthData.Bq 5031 = (249978894067615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5031 = 249978894067615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5031 = (13031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5031
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5032) ≤ val WuPaper.ClassicalFourthData.Bq 5032
    have hp : val WuPaper.ClassicalFourthData.Bq 5032 = (249993697276695:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5032 = 249993697276695 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5032 = (1629:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5033) ≤ val WuPaper.ClassicalFourthData.Bq 5033
    have hp : val WuPaper.ClassicalFourthData.Bq 5033 = (250008494451874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5033 = 250008494451874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5033 = (13033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5034) ≤ val WuPaper.ClassicalFourthData.Bq 5034
    have hp : val WuPaper.ClassicalFourthData.Bq 5034 = (250023285595373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5034 = 250023285595373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5034 = (6517:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5035) ≤ val WuPaper.ClassicalFourthData.Bq 5035
    have hp : val WuPaper.ClassicalFourthData.Bq 5035 = (250038070709414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5035 = 250038070709414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5035 = (2607:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5036) ≤ val WuPaper.ClassicalFourthData.Bq 5036
    have hp : val WuPaper.ClassicalFourthData.Bq 5036 = (250052849796216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5036 = 250052849796216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5036 = (3259:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5037) ≤ val WuPaper.ClassicalFourthData.Bq 5037
    have hp : val WuPaper.ClassicalFourthData.Bq 5037 = (250067622857998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5037 = 250067622857998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5037 = (13037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5038) ≤ val WuPaper.ClassicalFourthData.Bq 5038
    have hp : val WuPaper.ClassicalFourthData.Bq 5038 = (250082389896978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5038 = 250082389896978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5038 = (6519:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5039) ≤ val WuPaper.ClassicalFourthData.Bq 5039
    have hp : val WuPaper.ClassicalFourthData.Bq 5039 = (250097150915372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5039 = 250097150915372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5039 = (13039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_314
