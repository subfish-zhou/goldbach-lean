import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints070
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_070 (j : Fin 16) (hj : 16*70+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*70+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*70+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1120) ≤ val WuPaper.ClassicalFourthData.Bq 1120
    have hp : val WuPaper.ClassicalFourthData.Bq 1120 = (108271964005056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1120 = 108271964005056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1120 = (57:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1121) ≤ val WuPaper.ClassicalFourthData.Bq 1121
    have hp : val WuPaper.ClassicalFourthData.Bq 1121 = (108345739002532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1121 = 108345739002532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1121 = (9121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1122) ≤ val WuPaper.ClassicalFourthData.Bq 1122
    have hp : val WuPaper.ClassicalFourthData.Bq 1122 = (108419481103900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1122 = 108419481103900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1122 = (4561:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1123) ≤ val WuPaper.ClassicalFourthData.Bq 1123
    have hp : val WuPaper.ClassicalFourthData.Bq 1123 = (108493190326505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1123 = 108493190326505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1123 = (9123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1124) ≤ val WuPaper.ClassicalFourthData.Bq 1124
    have hp : val WuPaper.ClassicalFourthData.Bq 1124 = (108566866687680:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1124 = 108566866687680 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1124 = (2281:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1125) ≤ val WuPaper.ClassicalFourthData.Bq 1125
    have hp : val WuPaper.ClassicalFourthData.Bq 1125 = (108640510204748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1125 = 108640510204748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1125 = (73:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1126) ≤ val WuPaper.ClassicalFourthData.Bq 1126
    have hp : val WuPaper.ClassicalFourthData.Bq 1126 = (108714120895021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1126 = 108714120895021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1126 = (4563:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1127) ≤ val WuPaper.ClassicalFourthData.Bq 1127
    have hp : val WuPaper.ClassicalFourthData.Bq 1127 = (108787698775797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1127 = 108787698775797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1127 = (9127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1127
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1128) ≤ val WuPaper.ClassicalFourthData.Bq 1128
    have hp : val WuPaper.ClassicalFourthData.Bq 1128 = (108861243864364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1128 = 108861243864364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1128 = (1141:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1129) ≤ val WuPaper.ClassicalFourthData.Bq 1129
    have hp : val WuPaper.ClassicalFourthData.Bq 1129 = (108934756178001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1129 = 108934756178001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1129 = (9129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1130) ≤ val WuPaper.ClassicalFourthData.Bq 1130
    have hp : val WuPaper.ClassicalFourthData.Bq 1130 = (109008235733971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1130 = 109008235733971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1130 = (913:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1131) ≤ val WuPaper.ClassicalFourthData.Bq 1131
    have hp : val WuPaper.ClassicalFourthData.Bq 1131 = (109081682549529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1131 = 109081682549529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1131 = (9131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1132) ≤ val WuPaper.ClassicalFourthData.Bq 1132
    have hp : val WuPaper.ClassicalFourthData.Bq 1132 = (109155096641919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1132 = 109155096641919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1132 = (2283:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1133) ≤ val WuPaper.ClassicalFourthData.Bq 1133
    have hp : val WuPaper.ClassicalFourthData.Bq 1133 = (109228478028370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1133 = 109228478028370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1133 = (9133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1134) ≤ val WuPaper.ClassicalFourthData.Bq 1134
    have hp : val WuPaper.ClassicalFourthData.Bq 1134 = (109301826726104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1134 = 109301826726104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1134 = (4567:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1135) ≤ val WuPaper.ClassicalFourthData.Bq 1135
    have hp : val WuPaper.ClassicalFourthData.Bq 1135 = (109375142752329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1135 = 109375142752329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1135 = (1827:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_070
