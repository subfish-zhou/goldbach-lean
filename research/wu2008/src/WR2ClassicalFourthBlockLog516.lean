import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints516
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_516 (j : Fin 16) (hj : 16*516+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*516+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*516+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8256) ≤ val WuPaper.ClassicalFourthData.Bq 8256
    have hp : val WuPaper.ClassicalFourthData.Bq 8256 = (275521961585302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8256 = 275521961585302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8256 = (508:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8257) ≤ val WuPaper.ClassicalFourthData.Bq 8257
    have hp : val WuPaper.ClassicalFourthData.Bq 8257 = (275525088575622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8257 = 275525088575622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8257 = (16257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8258) ≤ val WuPaper.ClassicalFourthData.Bq 8258
    have hp : val WuPaper.ClassicalFourthData.Bq 8258 = (275528213543607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8258 = 275528213543607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8258 = (8129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8259) ≤ val WuPaper.ClassicalFourthData.Bq 8259
    have hp : val WuPaper.ClassicalFourthData.Bq 8259 = (275531336489899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8259 = 275531336489899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8259 = (16259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8260) ≤ val WuPaper.ClassicalFourthData.Bq 8260
    have hp : val WuPaper.ClassicalFourthData.Bq 8260 = (275534457415138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8260 = 275534457415138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8260 = (813:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8261) ≤ val WuPaper.ClassicalFourthData.Bq 8261
    have hp : val WuPaper.ClassicalFourthData.Bq 8261 = (275537576319962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8261 = 275537576319962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8261 = (16261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8262) ≤ val WuPaper.ClassicalFourthData.Bq 8262
    have hp : val WuPaper.ClassicalFourthData.Bq 8262 = (275540693205014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8262 = 275540693205014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8262 = (8131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8263) ≤ val WuPaper.ClassicalFourthData.Bq 8263
    have hp : val WuPaper.ClassicalFourthData.Bq 8263 = (275543808070930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8263 = 275543808070930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8263 = (16263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8264) ≤ val WuPaper.ClassicalFourthData.Bq 8264
    have hp : val WuPaper.ClassicalFourthData.Bq 8264 = (275546920918351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8264 = 275546920918351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8264 = (2033:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8265) ≤ val WuPaper.ClassicalFourthData.Bq 8265
    have hp : val WuPaper.ClassicalFourthData.Bq 8265 = (275550031747917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8265 = 275550031747917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8265 = (3253:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8266) ≤ val WuPaper.ClassicalFourthData.Bq 8266
    have hp : val WuPaper.ClassicalFourthData.Bq 8266 = (275553140560264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8266 = 275553140560264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8266 = (8133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8267) ≤ val WuPaper.ClassicalFourthData.Bq 8267
    have hp : val WuPaper.ClassicalFourthData.Bq 8267 = (275556247356033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8267 = 275556247356033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8267 = (16267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8268) ≤ val WuPaper.ClassicalFourthData.Bq 8268
    have hp : val WuPaper.ClassicalFourthData.Bq 8268 = (275559352135860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8268 = 275559352135860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8268 = (4067:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8269) ≤ val WuPaper.ClassicalFourthData.Bq 8269
    have hp : val WuPaper.ClassicalFourthData.Bq 8269 = (275562454900386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8269 = 275562454900386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8269 = (16269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8270) ≤ val WuPaper.ClassicalFourthData.Bq 8270
    have hp : val WuPaper.ClassicalFourthData.Bq 8270 = (275565555650246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8270 = 275565555650246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8270 = (1627:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8271) ≤ val WuPaper.ClassicalFourthData.Bq 8271
    have hp : val WuPaper.ClassicalFourthData.Bq 8271 = (275568654386080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8271 = 275568654386080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8271 = (16271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_516
