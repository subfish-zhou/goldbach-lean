import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints074
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_074 (j : Fin 16) (hj : 16*74+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*74+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*74+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1184) ≤ val WuPaper.ClassicalFourthData.Bq 1184
    have hp : val WuPaper.ClassicalFourthData.Bq 1184 = (112927960770943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1184 = 112927960770943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1184 = (287:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1185) ≤ val WuPaper.ClassicalFourthData.Bq 1185
    have hp : val WuPaper.ClassicalFourthData.Bq 1185 = (112999664915232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1185 = 112999664915232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1185 = (1837:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1186) ≤ val WuPaper.ClassicalFourthData.Bq 1186
    have hp : val WuPaper.ClassicalFourthData.Bq 1186 = (113071337250853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1186 = 113071337250853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1186 = (4593:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1187) ≤ val WuPaper.ClassicalFourthData.Bq 1187
    have hp : val WuPaper.ClassicalFourthData.Bq 1187 = (113142977794437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1187 = 113142977794437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1187 = (9187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1188) ≤ val WuPaper.ClassicalFourthData.Bq 1188
    have hp : val WuPaper.ClassicalFourthData.Bq 1188 = (113214586562607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1188 = 113214586562607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1188 = (2297:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1189) ≤ val WuPaper.ClassicalFourthData.Bq 1189
    have hp : val WuPaper.ClassicalFourthData.Bq 1189 = (113286163571972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1189 = 113286163571972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1189 = (9189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1190) ≤ val WuPaper.ClassicalFourthData.Bq 1190
    have hp : val WuPaper.ClassicalFourthData.Bq 1190 = (113357708839133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1190 = 113357708839133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1190 = (919:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1191) ≤ val WuPaper.ClassicalFourthData.Bq 1191
    have hp : val WuPaper.ClassicalFourthData.Bq 1191 = (113429222380678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1191 = 113429222380678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1191 = (9191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1191
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1192) ≤ val WuPaper.ClassicalFourthData.Bq 1192
    have hp : val WuPaper.ClassicalFourthData.Bq 1192 = (113500704213185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1192 = 113500704213185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1192 = (1149:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1193) ≤ val WuPaper.ClassicalFourthData.Bq 1193
    have hp : val WuPaper.ClassicalFourthData.Bq 1193 = (113572154353222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1193 = 113572154353222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1193 = (9193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1194) ≤ val WuPaper.ClassicalFourthData.Bq 1194
    have hp : val WuPaper.ClassicalFourthData.Bq 1194 = (113643572817345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1194 = 113643572817345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1194 = (4597:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1195) ≤ val WuPaper.ClassicalFourthData.Bq 1195
    have hp : val WuPaper.ClassicalFourthData.Bq 1195 = (113714959622100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1195 = 113714959622100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1195 = (1839:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1196) ≤ val WuPaper.ClassicalFourthData.Bq 1196
    have hp : val WuPaper.ClassicalFourthData.Bq 1196 = (113786314784021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1196 = 113786314784021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1196 = (2299:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1197) ≤ val WuPaper.ClassicalFourthData.Bq 1197
    have hp : val WuPaper.ClassicalFourthData.Bq 1197 = (113857638319633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1197 = 113857638319633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1197 = (9197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1198) ≤ val WuPaper.ClassicalFourthData.Bq 1198
    have hp : val WuPaper.ClassicalFourthData.Bq 1198 = (113928930245449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1198 = 113928930245449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1198 = (4599:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1199) ≤ val WuPaper.ClassicalFourthData.Bq 1199
    have hp : val WuPaper.ClassicalFourthData.Bq 1199 = (114000190577971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1199 = 114000190577971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1199 = (9199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_074
