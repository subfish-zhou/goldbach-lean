import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints078
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_078 (j : Fin 16) (hj : 16*78+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*78+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*78+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1248) ≤ val WuPaper.ClassicalFourthData.Bq 1248
    have hp : val WuPaper.ClassicalFourthData.Bq 1248 = (117453585865873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1248 = 117453585865873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1248 = (289:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1249) ≤ val WuPaper.ClassicalFourthData.Bq 1249
    have hp : val WuPaper.ClassicalFourthData.Bq 1249 = (117523287339290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1249 = 117523287339290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1249 = (9249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1250) ≤ val WuPaper.ClassicalFourthData.Bq 1250
    have hp : val WuPaper.ClassicalFourthData.Bq 1250 = (117592958046981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1250 = 117592958046981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1250 = (37:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1251) ≤ val WuPaper.ClassicalFourthData.Bq 1251
    have hp : val WuPaper.ClassicalFourthData.Bq 1251 = (117662598004900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1251 = 117662598004900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1251 = (9251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1252) ≤ val WuPaper.ClassicalFourthData.Bq 1252
    have hp : val WuPaper.ClassicalFourthData.Bq 1252 = (117732207228993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1252 = 117732207228993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1252 = (2313:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1253) ≤ val WuPaper.ClassicalFourthData.Bq 1253
    have hp : val WuPaper.ClassicalFourthData.Bq 1253 = (117801785735193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1253 = 117801785735193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1253 = (9253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1254) ≤ val WuPaper.ClassicalFourthData.Bq 1254
    have hp : val WuPaper.ClassicalFourthData.Bq 1254 = (117871333539425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1254 = 117871333539425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1254 = (4627:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1255) ≤ val WuPaper.ClassicalFourthData.Bq 1255
    have hp : val WuPaper.ClassicalFourthData.Bq 1255 = (117940850657601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1255 = 117940850657601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1255 = (1851:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1255
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1256) ≤ val WuPaper.ClassicalFourthData.Bq 1256
    have hp : val WuPaper.ClassicalFourthData.Bq 1256 = (118010337105627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1256 = 118010337105627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1256 = (1157:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1257) ≤ val WuPaper.ClassicalFourthData.Bq 1257
    have hp : val WuPaper.ClassicalFourthData.Bq 1257 = (118079792899394:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1257 = 118079792899394 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1257 = (9257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1258) ≤ val WuPaper.ClassicalFourthData.Bq 1258
    have hp : val WuPaper.ClassicalFourthData.Bq 1258 = (118149218054785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1258 = 118149218054785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1258 = (4629:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1259) ≤ val WuPaper.ClassicalFourthData.Bq 1259
    have hp : val WuPaper.ClassicalFourthData.Bq 1259 = (118218612587674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1259 = 118218612587674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1259 = (9259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1260) ≤ val WuPaper.ClassicalFourthData.Bq 1260
    have hp : val WuPaper.ClassicalFourthData.Bq 1260 = (118287976513922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1260 = 118287976513922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1260 = (463:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1261) ≤ val WuPaper.ClassicalFourthData.Bq 1261
    have hp : val WuPaper.ClassicalFourthData.Bq 1261 = (118357309849382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1261 = 118357309849382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1261 = (9261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1262) ≤ val WuPaper.ClassicalFourthData.Bq 1262
    have hp : val WuPaper.ClassicalFourthData.Bq 1262 = (118426612609895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1262 = 118426612609895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1262 = (4631:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1263) ≤ val WuPaper.ClassicalFourthData.Bq 1263
    have hp : val WuPaper.ClassicalFourthData.Bq 1263 = (118495884811293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1263 = 118495884811293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1263 = (9263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_078
