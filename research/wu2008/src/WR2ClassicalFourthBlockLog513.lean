import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints513
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_513 (j : Fin 16) (hj : 16*513+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*513+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*513+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8208) ≤ val WuPaper.ClassicalFourthData.Bq 8208
    have hp : val WuPaper.ClassicalFourthData.Bq 8208 = (275369475179204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8208 = 275369475179204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8208 = (1013:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8209) ≤ val WuPaper.ClassicalFourthData.Bq 8209
    have hp : val WuPaper.ClassicalFourthData.Bq 8209 = (275372699998954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8209 = 275372699998954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8209 = (16209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8210) ≤ val WuPaper.ClassicalFourthData.Bq 8210
    have hp : val WuPaper.ClassicalFourthData.Bq 8210 = (275375922765370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8210 = 275375922765370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8210 = (1621:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8211) ≤ val WuPaper.ClassicalFourthData.Bq 8211
    have hp : val WuPaper.ClassicalFourthData.Bq 8211 = (275379143479105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8211 = 275379143479105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8211 = (16211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8212) ≤ val WuPaper.ClassicalFourthData.Bq 8212
    have hp : val WuPaper.ClassicalFourthData.Bq 8212 = (275382362140808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8212 = 275382362140808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8212 = (4053:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8213) ≤ val WuPaper.ClassicalFourthData.Bq 8213
    have hp : val WuPaper.ClassicalFourthData.Bq 8213 = (275385578751132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8213 = 275385578751132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8213 = (16213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8214) ≤ val WuPaper.ClassicalFourthData.Bq 8214
    have hp : val WuPaper.ClassicalFourthData.Bq 8214 = (275388793310725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8214 = 275388793310725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8214 = (8107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8215) ≤ val WuPaper.ClassicalFourthData.Bq 8215
    have hp : val WuPaper.ClassicalFourthData.Bq 8215 = (275392005820239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8215 = 275392005820239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8215 = (3243:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8216) ≤ val WuPaper.ClassicalFourthData.Bq 8216
    have hp : val WuPaper.ClassicalFourthData.Bq 8216 = (275395216280323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8216 = 275395216280323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8216 = (2027:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8217) ≤ val WuPaper.ClassicalFourthData.Bq 8217
    have hp : val WuPaper.ClassicalFourthData.Bq 8217 = (275398424691627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8217 = 275398424691627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8217 = (16217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8218) ≤ val WuPaper.ClassicalFourthData.Bq 8218
    have hp : val WuPaper.ClassicalFourthData.Bq 8218 = (275401631054801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8218 = 275401631054801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8218 = (8109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8219) ≤ val WuPaper.ClassicalFourthData.Bq 8219
    have hp : val WuPaper.ClassicalFourthData.Bq 8219 = (275404835370493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8219 = 275404835370493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8219 = (16219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8220) ≤ val WuPaper.ClassicalFourthData.Bq 8220
    have hp : val WuPaper.ClassicalFourthData.Bq 8220 = (275408037639354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8220 = 275408037639354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8220 = (811:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8221) ≤ val WuPaper.ClassicalFourthData.Bq 8221
    have hp : val WuPaper.ClassicalFourthData.Bq 8221 = (275411237862031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8221 = 275411237862031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8221 = (16221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8222) ≤ val WuPaper.ClassicalFourthData.Bq 8222
    have hp : val WuPaper.ClassicalFourthData.Bq 8222 = (275414436039174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8222 = 275414436039174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8222 = (8111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8223) ≤ val WuPaper.ClassicalFourthData.Bq 8223
    have hp : val WuPaper.ClassicalFourthData.Bq 8223 = (275417632171431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8223 = 275417632171431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8223 = (16223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_513
