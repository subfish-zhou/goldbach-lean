import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints076
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_076 (j : Fin 16) (hj : 16*76+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*76+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*76+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1216) ≤ val WuPaper.ClassicalFourthData.Bq 1216
    have hp : val WuPaper.ClassicalFourthData.Bq 1216 = (115206798396034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1216 = 115206798396034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1216 = (288:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1217) ≤ val WuPaper.ClassicalFourthData.Bq 1217
    have hp : val WuPaper.ClassicalFourthData.Bq 1217 = (115277492859007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1217 = 115277492859007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1217 = (9217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1218) ≤ val WuPaper.ClassicalFourthData.Bq 1218
    have hp : val WuPaper.ClassicalFourthData.Bq 1218 = (115348156040203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1218 = 115348156040203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1218 = (4609:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1219) ≤ val WuPaper.ClassicalFourthData.Bq 1219
    have hp : val WuPaper.ClassicalFourthData.Bq 1219 = (115418787955911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1219 = 115418787955911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1219 = (9219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1220) ≤ val WuPaper.ClassicalFourthData.Bq 1220
    have hp : val WuPaper.ClassicalFourthData.Bq 1220 = (115489388622411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1220 = 115489388622411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1220 = (461:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1221) ≤ val WuPaper.ClassicalFourthData.Bq 1221
    have hp : val WuPaper.ClassicalFourthData.Bq 1221 = (115559958055970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1221 = 115559958055970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1221 = (9221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1222) ≤ val WuPaper.ClassicalFourthData.Bq 1222
    have hp : val WuPaper.ClassicalFourthData.Bq 1222 = (115630496272847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1222 = 115630496272847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1222 = (4611:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1223) ≤ val WuPaper.ClassicalFourthData.Bq 1223
    have hp : val WuPaper.ClassicalFourthData.Bq 1223 = (115701003289286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1223 = 115701003289286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1223 = (9223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1223
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1224) ≤ val WuPaper.ClassicalFourthData.Bq 1224
    have hp : val WuPaper.ClassicalFourthData.Bq 1224 = (115771479121527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1224 = 115771479121527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1224 = (1153:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1225) ≤ val WuPaper.ClassicalFourthData.Bq 1225
    have hp : val WuPaper.ClassicalFourthData.Bq 1225 = (115841923785793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1225 = 115841923785793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1225 = (369:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1226) ≤ val WuPaper.ClassicalFourthData.Bq 1226
    have hp : val WuPaper.ClassicalFourthData.Bq 1226 = (115912337298301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1226 = 115912337298301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1226 = (4613:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1227) ≤ val WuPaper.ClassicalFourthData.Bq 1227
    have hp : val WuPaper.ClassicalFourthData.Bq 1227 = (115982719675255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1227 = 115982719675255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1227 = (9227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1228) ≤ val WuPaper.ClassicalFourthData.Bq 1228
    have hp : val WuPaper.ClassicalFourthData.Bq 1228 = (116053070932850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1228 = 116053070932850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1228 = (2307:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1229) ≤ val WuPaper.ClassicalFourthData.Bq 1229
    have hp : val WuPaper.ClassicalFourthData.Bq 1229 = (116123391087270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1229 = 116123391087270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1229 = (9229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1230) ≤ val WuPaper.ClassicalFourthData.Bq 1230
    have hp : val WuPaper.ClassicalFourthData.Bq 1230 = (116193680154688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1230 = 116193680154688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1230 = (923:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1231) ≤ val WuPaper.ClassicalFourthData.Bq 1231
    have hp : val WuPaper.ClassicalFourthData.Bq 1231 = (116263938151266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1231 = 116263938151266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1231 = (9231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_076
