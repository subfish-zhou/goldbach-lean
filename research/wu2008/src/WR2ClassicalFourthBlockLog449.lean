import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints449
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_449 (j : Fin 16) (hj : 16*449+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*449+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*449+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7184) ≤ val WuPaper.ClassicalFourthData.Bq 7184
    have hp : val WuPaper.ClassicalFourthData.Bq 7184 = (270861386820856:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7184 = 270861386820856 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7184 = (949:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7185) ≤ val WuPaper.ClassicalFourthData.Bq 7185
    have hp : val WuPaper.ClassicalFourthData.Bq 7185 = (270867101434998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7185 = 270867101434998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7185 = (3037:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7186) ≤ val WuPaper.ClassicalFourthData.Bq 7186
    have hp : val WuPaper.ClassicalFourthData.Bq 7186 = (270872813191074:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7186 = 270872813191074 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7186 = (7593:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7187) ≤ val WuPaper.ClassicalFourthData.Bq 7187
    have hp : val WuPaper.ClassicalFourthData.Bq 7187 = (270878522090028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7187 = 270878522090028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7187 = (15187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7188) ≤ val WuPaper.ClassicalFourthData.Bq 7188
    have hp : val WuPaper.ClassicalFourthData.Bq 7188 = (270884228132798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7188 = 270884228132798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7188 = (3797:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7189) ≤ val WuPaper.ClassicalFourthData.Bq 7189
    have hp : val WuPaper.ClassicalFourthData.Bq 7189 = (270889931320325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7189 = 270889931320325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7189 = (15189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7190) ≤ val WuPaper.ClassicalFourthData.Bq 7190
    have hp : val WuPaper.ClassicalFourthData.Bq 7190 = (270895631653550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7190 = 270895631653550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7190 = (1519:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7191) ≤ val WuPaper.ClassicalFourthData.Bq 7191
    have hp : val WuPaper.ClassicalFourthData.Bq 7191 = (270901329133411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7191 = 270901329133411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7191 = (15191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7191
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7192) ≤ val WuPaper.ClassicalFourthData.Bq 7192
    have hp : val WuPaper.ClassicalFourthData.Bq 7192 = (270907023760849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7192 = 270907023760849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7192 = (1899:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7193) ≤ val WuPaper.ClassicalFourthData.Bq 7193
    have hp : val WuPaper.ClassicalFourthData.Bq 7193 = (270912715536801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7193 = 270912715536801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7193 = (15193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7194) ≤ val WuPaper.ClassicalFourthData.Bq 7194
    have hp : val WuPaper.ClassicalFourthData.Bq 7194 = (270918404462207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7194 = 270918404462207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7194 = (7597:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7195) ≤ val WuPaper.ClassicalFourthData.Bq 7195
    have hp : val WuPaper.ClassicalFourthData.Bq 7195 = (270924090538005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7195 = 270924090538005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7195 = (3039:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7196) ≤ val WuPaper.ClassicalFourthData.Bq 7196
    have hp : val WuPaper.ClassicalFourthData.Bq 7196 = (270929773765132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7196 = 270929773765132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7196 = (3799:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7197) ≤ val WuPaper.ClassicalFourthData.Bq 7197
    have hp : val WuPaper.ClassicalFourthData.Bq 7197 = (270935454144525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7197 = 270935454144525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7197 = (15197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7198) ≤ val WuPaper.ClassicalFourthData.Bq 7198
    have hp : val WuPaper.ClassicalFourthData.Bq 7198 = (270941131677124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7198 = 270941131677124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7198 = (7599:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7199) ≤ val WuPaper.ClassicalFourthData.Bq 7199
    have hp : val WuPaper.ClassicalFourthData.Bq 7199 = (270946806363863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7199 = 270946806363863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7199 = (15199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_449
