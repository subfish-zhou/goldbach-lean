import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints439
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_439 (j : Fin 16) (hj : 16*439+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*439+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*439+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7024) ≤ val WuPaper.ClassicalFourthData.Bq 7024
    have hp : val WuPaper.ClassicalFourthData.Bq 7024 = (269909572191610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7024 = 269909572191610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7024 = (939:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7025) ≤ val WuPaper.ClassicalFourthData.Bq 7025
    have hp : val WuPaper.ClassicalFourthData.Bq 7025 = (269915756462774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7025 = 269915756462774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7025 = (601:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7026) ≤ val WuPaper.ClassicalFourthData.Bq 7026
    have hp : val WuPaper.ClassicalFourthData.Bq 7026 = (269921937720718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7026 = 269921937720718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7026 = (7513:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7027) ≤ val WuPaper.ClassicalFourthData.Bq 7027
    have hp : val WuPaper.ClassicalFourthData.Bq 7027 = (269928115966441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7027 = 269928115966441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7027 = (15027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7028) ≤ val WuPaper.ClassicalFourthData.Bq 7028
    have hp : val WuPaper.ClassicalFourthData.Bq 7028 = (269934291200941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7028 = 269934291200941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7028 = (3757:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7029) ≤ val WuPaper.ClassicalFourthData.Bq 7029
    have hp : val WuPaper.ClassicalFourthData.Bq 7029 = (269940463425217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7029 = 269940463425217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7029 = (15029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7030) ≤ val WuPaper.ClassicalFourthData.Bq 7030
    have hp : val WuPaper.ClassicalFourthData.Bq 7030 = (269946632640266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7030 = 269946632640266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7030 = (1503:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7031) ≤ val WuPaper.ClassicalFourthData.Bq 7031
    have hp : val WuPaper.ClassicalFourthData.Bq 7031 = (269952798847085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7031 = 269952798847085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7031 = (15031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7031
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7032) ≤ val WuPaper.ClassicalFourthData.Bq 7032
    have hp : val WuPaper.ClassicalFourthData.Bq 7032 = (269958962046671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7032 = 269958962046671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7032 = (1879:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7033) ≤ val WuPaper.ClassicalFourthData.Bq 7033
    have hp : val WuPaper.ClassicalFourthData.Bq 7033 = (269965122240021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7033 = 269965122240021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7033 = (15033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7034) ≤ val WuPaper.ClassicalFourthData.Bq 7034
    have hp : val WuPaper.ClassicalFourthData.Bq 7034 = (269971279428131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7034 = 269971279428131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7034 = (7517:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7035) ≤ val WuPaper.ClassicalFourthData.Bq 7035
    have hp : val WuPaper.ClassicalFourthData.Bq 7035 = (269977433611996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7035 = 269977433611996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7035 = (3007:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7036) ≤ val WuPaper.ClassicalFourthData.Bq 7036
    have hp : val WuPaper.ClassicalFourthData.Bq 7036 = (269983584792613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7036 = 269983584792613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7036 = (3759:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7037) ≤ val WuPaper.ClassicalFourthData.Bq 7037
    have hp : val WuPaper.ClassicalFourthData.Bq 7037 = (269989732970976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7037 = 269989732970976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7037 = (15037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7038) ≤ val WuPaper.ClassicalFourthData.Bq 7038
    have hp : val WuPaper.ClassicalFourthData.Bq 7038 = (269995878148079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7038 = 269995878148079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7038 = (7519:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7039) ≤ val WuPaper.ClassicalFourthData.Bq 7039
    have hp : val WuPaper.ClassicalFourthData.Bq 7039 = (270002020324918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7039 = 270002020324918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7039 = (15039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_439
