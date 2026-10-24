import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints073
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_073 (j : Fin 16) (hj : 16*73+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*73+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*73+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1168) ≤ val WuPaper.ClassicalFourthData.Bq 1168
    have hp : val WuPaper.ClassicalFourthData.Bq 1168 = (111776354869289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1168 = 111776354869289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1168 = (573:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1169) ≤ val WuPaper.ClassicalFourthData.Bq 1169
    have hp : val WuPaper.ClassicalFourthData.Bq 1169 = (111848570223149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1169 = 111848570223149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1169 = (9169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1170) ≤ val WuPaper.ClassicalFourthData.Bq 1170
    have hp : val WuPaper.ClassicalFourthData.Bq 1170 = (111920753500741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1170 = 111920753500741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1170 = (917:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1171) ≤ val WuPaper.ClassicalFourthData.Bq 1171
    have hp : val WuPaper.ClassicalFourthData.Bq 1171 = (111992904718873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1171 = 111992904718873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1171 = (9171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1172) ≤ val WuPaper.ClassicalFourthData.Bq 1172
    have hp : val WuPaper.ClassicalFourthData.Bq 1172 = (112065023894340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1172 = 112065023894340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1172 = (2293:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1173) ≤ val WuPaper.ClassicalFourthData.Bq 1173
    have hp : val WuPaper.ClassicalFourthData.Bq 1173 = (112137111043928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1173 = 112137111043928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1173 = (9173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1174) ≤ val WuPaper.ClassicalFourthData.Bq 1174
    have hp : val WuPaper.ClassicalFourthData.Bq 1174 = (112209166184412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1174 = 112209166184412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1174 = (4587:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1175) ≤ val WuPaper.ClassicalFourthData.Bq 1175
    have hp : val WuPaper.ClassicalFourthData.Bq 1175 = (112281189332553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1175 = 112281189332553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1175 = (367:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1175
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1176) ≤ val WuPaper.ClassicalFourthData.Bq 1176
    have hp : val WuPaper.ClassicalFourthData.Bq 1176 = (112353180505105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1176 = 112353180505105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1176 = (1147:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1177) ≤ val WuPaper.ClassicalFourthData.Bq 1177
    have hp : val WuPaper.ClassicalFourthData.Bq 1177 = (112425139718808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1177 = 112425139718808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1177 = (9177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1178) ≤ val WuPaper.ClassicalFourthData.Bq 1178
    have hp : val WuPaper.ClassicalFourthData.Bq 1178 = (112497066990393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1178 = 112497066990393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1178 = (4589:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1179) ≤ val WuPaper.ClassicalFourthData.Bq 1179
    have hp : val WuPaper.ClassicalFourthData.Bq 1179 = (112568962336579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1179 = 112568962336579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1179 = (9179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1180) ≤ val WuPaper.ClassicalFourthData.Bq 1180
    have hp : val WuPaper.ClassicalFourthData.Bq 1180 = (112640825774075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1180 = 112640825774075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1180 = (459:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1181) ≤ val WuPaper.ClassicalFourthData.Bq 1181
    have hp : val WuPaper.ClassicalFourthData.Bq 1181 = (112712657319578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1181 = 112712657319578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1181 = (9181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1182) ≤ val WuPaper.ClassicalFourthData.Bq 1182
    have hp : val WuPaper.ClassicalFourthData.Bq 1182 = (112784456989775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1182 = 112784456989775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1182 = (4591:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1183) ≤ val WuPaper.ClassicalFourthData.Bq 1183
    have hp : val WuPaper.ClassicalFourthData.Bq 1183 = (112856224801342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1183 = 112856224801342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1183 = (9183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_073
