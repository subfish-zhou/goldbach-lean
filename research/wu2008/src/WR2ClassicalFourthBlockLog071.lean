import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints071
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_071 (j : Fin 16) (hj : 16*71+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*71+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*71+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1136) ≤ val WuPaper.ClassicalFourthData.Bq 1136
    have hp : val WuPaper.ClassicalFourthData.Bq 1136 = (109448426124243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1136 = 109448426124243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1136 = (571:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1137) ≤ val WuPaper.ClassicalFourthData.Bq 1137
    have hp : val WuPaper.ClassicalFourthData.Bq 1137 = (109521676859031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1137 = 109521676859031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1137 = (9137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1138) ≤ val WuPaper.ClassicalFourthData.Bq 1138
    have hp : val WuPaper.ClassicalFourthData.Bq 1138 = (109594894973868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1138 = 109594894973868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1138 = (4569:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1139) ≤ val WuPaper.ClassicalFourthData.Bq 1139
    have hp : val WuPaper.ClassicalFourthData.Bq 1139 = (109668080485919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1139 = 109668080485919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1139 = (9139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1140) ≤ val WuPaper.ClassicalFourthData.Bq 1140
    have hp : val WuPaper.ClassicalFourthData.Bq 1140 = (109741233412334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1140 = 109741233412334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1140 = (457:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1141) ≤ val WuPaper.ClassicalFourthData.Bq 1141
    have hp : val WuPaper.ClassicalFourthData.Bq 1141 = (109814353770256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1141 = 109814353770256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1141 = (9141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1142) ≤ val WuPaper.ClassicalFourthData.Bq 1142
    have hp : val WuPaper.ClassicalFourthData.Bq 1142 = (109887441576814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1142 = 109887441576814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1142 = (4571:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1143) ≤ val WuPaper.ClassicalFourthData.Bq 1143
    have hp : val WuPaper.ClassicalFourthData.Bq 1143 = (109960496849126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1143 = 109960496849126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1143 = (9143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1143
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1144) ≤ val WuPaper.ClassicalFourthData.Bq 1144
    have hp : val WuPaper.ClassicalFourthData.Bq 1144 = (110033519604300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1144 = 110033519604300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1144 = (1143:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1145) ≤ val WuPaper.ClassicalFourthData.Bq 1145
    have hp : val WuPaper.ClassicalFourthData.Bq 1145 = (110106509859431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1145 = 110106509859431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1145 = (1829:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1146) ≤ val WuPaper.ClassicalFourthData.Bq 1146
    have hp : val WuPaper.ClassicalFourthData.Bq 1146 = (110179467631604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1146 = 110179467631604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1146 = (4573:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1147) ≤ val WuPaper.ClassicalFourthData.Bq 1147
    have hp : val WuPaper.ClassicalFourthData.Bq 1147 = (110252392937894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1147 = 110252392937894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1147 = (9147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1148) ≤ val WuPaper.ClassicalFourthData.Bq 1148
    have hp : val WuPaper.ClassicalFourthData.Bq 1148 = (110325285795361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1148 = 110325285795361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1148 = (2287:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1149) ≤ val WuPaper.ClassicalFourthData.Bq 1149
    have hp : val WuPaper.ClassicalFourthData.Bq 1149 = (110398146221058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1149 = 110398146221058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1149 = (9149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1150) ≤ val WuPaper.ClassicalFourthData.Bq 1150
    have hp : val WuPaper.ClassicalFourthData.Bq 1150 = (110470974232024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1150 = 110470974232024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1150 = (183:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1151) ≤ val WuPaper.ClassicalFourthData.Bq 1151
    have hp : val WuPaper.ClassicalFourthData.Bq 1151 = (110543769845288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1151 = 110543769845288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1151 = (9151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_071
