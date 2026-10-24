import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints260
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_260 (j : Fin 16) (hj : 16*260+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*260+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*260+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4160) ≤ val WuPaper.ClassicalFourthData.Bq 4160
    have hp : val WuPaper.ClassicalFourthData.Bq 4160 = (234522963110568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4160 = 234522963110568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4160 = (76:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4161) ≤ val WuPaper.ClassicalFourthData.Bq 4161
    have hp : val WuPaper.ClassicalFourthData.Bq 4161 = (234543984661530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4161 = 234543984661530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4161 = (12161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4162) ≤ val WuPaper.ClassicalFourthData.Bq 4162
    have hp : val WuPaper.ClassicalFourthData.Bq 4162 = (234564997817374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4162 = 234564997817374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4162 = (6081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4163) ≤ val WuPaper.ClassicalFourthData.Bq 4163
    have hp : val WuPaper.ClassicalFourthData.Bq 4163 = (234586002581380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4163 = 234586002581380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4163 = (12163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4164) ≤ val WuPaper.ClassicalFourthData.Bq 4164
    have hp : val WuPaper.ClassicalFourthData.Bq 4164 = (234606998956826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4164 = 234606998956826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4164 = (3041:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4165) ≤ val WuPaper.ClassicalFourthData.Bq 4165
    have hp : val WuPaper.ClassicalFourthData.Bq 4165 = (234627986946992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4165 = 234627986946992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4165 = (2433:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4166) ≤ val WuPaper.ClassicalFourthData.Bq 4166
    have hp : val WuPaper.ClassicalFourthData.Bq 4166 = (234648966555152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4166 = 234648966555152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4166 = (6083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4167) ≤ val WuPaper.ClassicalFourthData.Bq 4167
    have hp : val WuPaper.ClassicalFourthData.Bq 4167 = (234669937784581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4167 = 234669937784581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4167 = (12167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4168) ≤ val WuPaper.ClassicalFourthData.Bq 4168
    have hp : val WuPaper.ClassicalFourthData.Bq 4168 = (234690900638552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4168 = 234690900638552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4168 = (1521:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4169) ≤ val WuPaper.ClassicalFourthData.Bq 4169
    have hp : val WuPaper.ClassicalFourthData.Bq 4169 = (234711855120336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4169 = 234711855120336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4169 = (12169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4170) ≤ val WuPaper.ClassicalFourthData.Bq 4170
    have hp : val WuPaper.ClassicalFourthData.Bq 4170 = (234732801233204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4170 = 234732801233204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4170 = (1217:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4171) ≤ val WuPaper.ClassicalFourthData.Bq 4171
    have hp : val WuPaper.ClassicalFourthData.Bq 4171 = (234753738980423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4171 = 234753738980423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4171 = (12171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4172) ≤ val WuPaper.ClassicalFourthData.Bq 4172
    have hp : val WuPaper.ClassicalFourthData.Bq 4172 = (234774668365260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4172 = 234774668365260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4172 = (3043:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4173) ≤ val WuPaper.ClassicalFourthData.Bq 4173
    have hp : val WuPaper.ClassicalFourthData.Bq 4173 = (234795589390981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4173 = 234795589390981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4173 = (12173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4174) ≤ val WuPaper.ClassicalFourthData.Bq 4174
    have hp : val WuPaper.ClassicalFourthData.Bq 4174 = (234816502060850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4174 = 234816502060850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4174 = (6087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4175) ≤ val WuPaper.ClassicalFourthData.Bq 4175
    have hp : val WuPaper.ClassicalFourthData.Bq 4175 = (234837406378128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4175 = 234837406378128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4175 = (487:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_260
