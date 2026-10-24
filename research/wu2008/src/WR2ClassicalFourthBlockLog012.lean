import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints012
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_012 (j : Fin 16) (hj : 16*12+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*12+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*12+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 192) ≤ val WuPaper.ClassicalFourthData.Bq 192
    have hp : val WuPaper.ClassicalFourthData.Bq 192 = (22892375927174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 192 = 22892375927174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 192 = (256:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 193) ≤ val WuPaper.ClassicalFourthData.Bq 193
    have hp : val WuPaper.ClassicalFourthData.Bq 193 = (23006032988520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 193 = 23006032988520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 193 = (8193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 194) ≤ val WuPaper.ClassicalFourthData.Bq 194
    have hp : val WuPaper.ClassicalFourthData.Bq 194 = (23119634542269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 194 = 23119634542269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 194 = (4097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 195) ≤ val WuPaper.ClassicalFourthData.Bq 195
    have hp : val WuPaper.ClassicalFourthData.Bq 195 = (23233180621979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 195 = 23233180621979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 195 = (1639:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 196) ≤ val WuPaper.ClassicalFourthData.Bq 196
    have hp : val WuPaper.ClassicalFourthData.Bq 196 = (23346671261182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 196 = 23346671261182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 196 = (2049:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 197) ≤ val WuPaper.ClassicalFourthData.Bq 197
    have hp : val WuPaper.ClassicalFourthData.Bq 197 = (23460106493383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 197 = 23460106493383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 197 = (8197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 198) ≤ val WuPaper.ClassicalFourthData.Bq 198
    have hp : val WuPaper.ClassicalFourthData.Bq 198 = (23573486352062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 198 = 23573486352062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 198 = (4099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 199) ≤ val WuPaper.ClassicalFourthData.Bq 199
    have hp : val WuPaper.ClassicalFourthData.Bq 199 = (23686810870675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 199 = 23686810870675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 199 = (8199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 200) ≤ val WuPaper.ClassicalFourthData.Bq 200
    have hp : val WuPaper.ClassicalFourthData.Bq 200 = (23800080082650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 200 = 23800080082650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 200 = (41:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 201) ≤ val WuPaper.ClassicalFourthData.Bq 201
    have hp : val WuPaper.ClassicalFourthData.Bq 201 = (23913294021390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 201 = 23913294021390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 201 = (8201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 202) ≤ val WuPaper.ClassicalFourthData.Bq 202
    have hp : val WuPaper.ClassicalFourthData.Bq 202 = (24026452720273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 202 = 24026452720273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 202 = (4101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 203) ≤ val WuPaper.ClassicalFourthData.Bq 203
    have hp : val WuPaper.ClassicalFourthData.Bq 203 = (24139556212649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 203 = 24139556212649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 203 = (8203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 204) ≤ val WuPaper.ClassicalFourthData.Bq 204
    have hp : val WuPaper.ClassicalFourthData.Bq 204 = (24252604531845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 204 = 24252604531845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 204 = (2051:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 205) ≤ val WuPaper.ClassicalFourthData.Bq 205
    have hp : val WuPaper.ClassicalFourthData.Bq 205 = (24365597711162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 205 = 24365597711162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 205 = (1641:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 206) ≤ val WuPaper.ClassicalFourthData.Bq 206
    have hp : val WuPaper.ClassicalFourthData.Bq 206 = (24478535783874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 206 = 24478535783874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 206 = (4103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 207) ≤ val WuPaper.ClassicalFourthData.Bq 207
    have hp : val WuPaper.ClassicalFourthData.Bq 207 = (24591418783231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 207 = 24591418783231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 207 = (8207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_012
