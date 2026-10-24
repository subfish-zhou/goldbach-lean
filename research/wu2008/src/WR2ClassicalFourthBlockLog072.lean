import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints072
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_072 (j : Fin 16) (hj : 16*72+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*72+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*72+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1152) ≤ val WuPaper.ClassicalFourthData.Bq 1152
    have hp : val WuPaper.ClassicalFourthData.Bq 1152 = (110616533077868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1152 = 110616533077868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1152 = (286:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1153) ≤ val WuPaper.ClassicalFourthData.Bq 1153
    have hp : val WuPaper.ClassicalFourthData.Bq 1153 = (110689263946771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1153 = 110689263946771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1153 = (9153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1154) ≤ val WuPaper.ClassicalFourthData.Bq 1154
    have hp : val WuPaper.ClassicalFourthData.Bq 1154 = (110761962468990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1154 = 110761962468990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1154 = (4577:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1155) ≤ val WuPaper.ClassicalFourthData.Bq 1155
    have hp : val WuPaper.ClassicalFourthData.Bq 1155 = (110834628661511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1155 = 110834628661511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1155 = (1831:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1156) ≤ val WuPaper.ClassicalFourthData.Bq 1156
    have hp : val WuPaper.ClassicalFourthData.Bq 1156 = (110907262541307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1156 = 110907262541307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1156 = (2289:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1157) ≤ val WuPaper.ClassicalFourthData.Bq 1157
    have hp : val WuPaper.ClassicalFourthData.Bq 1157 = (110979864125339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1157 = 110979864125339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1157 = (9157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1158) ≤ val WuPaper.ClassicalFourthData.Bq 1158
    have hp : val WuPaper.ClassicalFourthData.Bq 1158 = (111052433430558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1158 = 111052433430558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1158 = (4579:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1159) ≤ val WuPaper.ClassicalFourthData.Bq 1159
    have hp : val WuPaper.ClassicalFourthData.Bq 1159 = (111124970473905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1159 = 111124970473905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1159 = (9159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1159
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1160) ≤ val WuPaper.ClassicalFourthData.Bq 1160
    have hp : val WuPaper.ClassicalFourthData.Bq 1160 = (111197475272307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1160 = 111197475272307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1160 = (229:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1161) ≤ val WuPaper.ClassicalFourthData.Bq 1161
    have hp : val WuPaper.ClassicalFourthData.Bq 1161 = (111269947842681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1161 = 111269947842681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1161 = (9161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1162) ≤ val WuPaper.ClassicalFourthData.Bq 1162
    have hp : val WuPaper.ClassicalFourthData.Bq 1162 = (111342388201935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1162 = 111342388201935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1162 = (4581:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1163) ≤ val WuPaper.ClassicalFourthData.Bq 1163
    have hp : val WuPaper.ClassicalFourthData.Bq 1163 = (111414796366964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1163 = 111414796366964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1163 = (9163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1164) ≤ val WuPaper.ClassicalFourthData.Bq 1164
    have hp : val WuPaper.ClassicalFourthData.Bq 1164 = (111487172354652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1164 = 111487172354652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1164 = (2291:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1165) ≤ val WuPaper.ClassicalFourthData.Bq 1165
    have hp : val WuPaper.ClassicalFourthData.Bq 1165 = (111559516181871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1165 = 111559516181871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1165 = (1833:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1166) ≤ val WuPaper.ClassicalFourthData.Bq 1166
    have hp : val WuPaper.ClassicalFourthData.Bq 1166 = (111631827865485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1166 = 111631827865485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1166 = (4583:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1167) ≤ val WuPaper.ClassicalFourthData.Bq 1167
    have hp : val WuPaper.ClassicalFourthData.Bq 1167 = (111704107422345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1167 = 111704107422345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1167 = (9167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_072
