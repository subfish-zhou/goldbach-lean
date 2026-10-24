import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints261
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_261 (j : Fin 16) (hj : 16*261+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*261+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*261+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4176) ≤ val WuPaper.ClassicalFourthData.Bq 4176
    have hp : val WuPaper.ClassicalFourthData.Bq 4176 = (234858302346077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4176 = 234858302346077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4176 = (761:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4177) ≤ val WuPaper.ClassicalFourthData.Bq 4177
    have hp : val WuPaper.ClassicalFourthData.Bq 4177 = (234879189967956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4177 = 234879189967956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4177 = (12177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4178) ≤ val WuPaper.ClassicalFourthData.Bq 4178
    have hp : val WuPaper.ClassicalFourthData.Bq 4178 = (234900069247023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4178 = 234900069247023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4178 = (6089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4179) ≤ val WuPaper.ClassicalFourthData.Bq 4179
    have hp : val WuPaper.ClassicalFourthData.Bq 4179 = (234920940186534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4179 = 234920940186534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4179 = (12179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4180) ≤ val WuPaper.ClassicalFourthData.Bq 4180
    have hp : val WuPaper.ClassicalFourthData.Bq 4180 = (234941802789743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4180 = 234941802789743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4180 = (609:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4181) ≤ val WuPaper.ClassicalFourthData.Bq 4181
    have hp : val WuPaper.ClassicalFourthData.Bq 4181 = (234962657059904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4181 = 234962657059904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4181 = (12181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4182) ≤ val WuPaper.ClassicalFourthData.Bq 4182
    have hp : val WuPaper.ClassicalFourthData.Bq 4182 = (234983503000269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4182 = 234983503000269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4182 = (6091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4183) ≤ val WuPaper.ClassicalFourthData.Bq 4183
    have hp : val WuPaper.ClassicalFourthData.Bq 4183 = (235004340614087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4183 = 235004340614087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4183 = (12183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4184) ≤ val WuPaper.ClassicalFourthData.Bq 4184
    have hp : val WuPaper.ClassicalFourthData.Bq 4184 = (235025169904608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4184 = 235025169904608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4184 = (1523:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4185) ≤ val WuPaper.ClassicalFourthData.Bq 4185
    have hp : val WuPaper.ClassicalFourthData.Bq 4185 = (235045990875079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4185 = 235045990875079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4185 = (2437:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4186) ≤ val WuPaper.ClassicalFourthData.Bq 4186
    have hp : val WuPaper.ClassicalFourthData.Bq 4186 = (235066803528745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4186 = 235066803528745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4186 = (6093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4187) ≤ val WuPaper.ClassicalFourthData.Bq 4187
    have hp : val WuPaper.ClassicalFourthData.Bq 4187 = (235087607868851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4187 = 235087607868851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4187 = (12187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4188) ≤ val WuPaper.ClassicalFourthData.Bq 4188
    have hp : val WuPaper.ClassicalFourthData.Bq 4188 = (235108403898639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4188 = 235108403898639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4188 = (3047:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4189) ≤ val WuPaper.ClassicalFourthData.Bq 4189
    have hp : val WuPaper.ClassicalFourthData.Bq 4189 = (235129191621351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4189 = 235129191621351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4189 = (12189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4190) ≤ val WuPaper.ClassicalFourthData.Bq 4190
    have hp : val WuPaper.ClassicalFourthData.Bq 4190 = (235149971040226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4190 = 235149971040226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4190 = (1219:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4191) ≤ val WuPaper.ClassicalFourthData.Bq 4191
    have hp : val WuPaper.ClassicalFourthData.Bq 4191 = (235170742158502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4191 = 235170742158502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4191 = (12191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_261
