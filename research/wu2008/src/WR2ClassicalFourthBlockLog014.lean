import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints014
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_014 (j : Fin 16) (hj : 16*14+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*14+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*14+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 224) ≤ val WuPaper.ClassicalFourthData.Bq 224
    have hp : val WuPaper.ClassicalFourthData.Bq 224 = (26502035644003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 224 = 26502035644003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 224 = (257:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 225) ≤ val WuPaper.ClassicalFourthData.Bq 225
    have hp : val WuPaper.ClassicalFourthData.Bq 225 = (26613932979573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 225 = 26613932979573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 225 = (329:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 226) ≤ val WuPaper.ClassicalFourthData.Bq 226
    have hp : val WuPaper.ClassicalFourthData.Bq 226 = (26725775868697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 226 = 26725775868697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 226 = (4113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 227) ≤ val WuPaper.ClassicalFourthData.Bq 227
    have hp : val WuPaper.ClassicalFourthData.Bq 227 = (26837564344117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 227 = 26837564344117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 227 = (8227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 228) ≤ val WuPaper.ClassicalFourthData.Bq 228
    have hp : val WuPaper.ClassicalFourthData.Bq 228 = (26949298438552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 228 = 26949298438552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 228 = (2057:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 229) ≤ val WuPaper.ClassicalFourthData.Bq 229
    have hp : val WuPaper.ClassicalFourthData.Bq 229 = (27060978184694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 229 = 27060978184694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 229 = (8229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 230) ≤ val WuPaper.ClassicalFourthData.Bq 230
    have hp : val WuPaper.ClassicalFourthData.Bq 230 = (27172603615211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 230 = 27172603615211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 230 = (823:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 231) ≤ val WuPaper.ClassicalFourthData.Bq 231
    have hp : val WuPaper.ClassicalFourthData.Bq 231 = (27284174762746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 231 = 27284174762746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 231 = (8231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 232) ≤ val WuPaper.ClassicalFourthData.Bq 232
    have hp : val WuPaper.ClassicalFourthData.Bq 232 = (27395691659917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 232 = 27395691659917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 232 = (1029:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 233) ≤ val WuPaper.ClassicalFourthData.Bq 233
    have hp : val WuPaper.ClassicalFourthData.Bq 233 = (27507154339316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 233 = 27507154339316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 233 = (8233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 234) ≤ val WuPaper.ClassicalFourthData.Bq 234
    have hp : val WuPaper.ClassicalFourthData.Bq 234 = (27618562833512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 234 = 27618562833512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 234 = (4117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 235) ≤ val WuPaper.ClassicalFourthData.Bq 235
    have hp : val WuPaper.ClassicalFourthData.Bq 235 = (27729917175047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 235 = 27729917175047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 235 = (1647:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 236) ≤ val WuPaper.ClassicalFourthData.Bq 236
    have hp : val WuPaper.ClassicalFourthData.Bq 236 = (27841217396440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 236 = 27841217396440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 236 = (2059:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 237) ≤ val WuPaper.ClassicalFourthData.Bq 237
    have hp : val WuPaper.ClassicalFourthData.Bq 237 = (27952463530185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 237 = 27952463530185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 237 = (8237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 238) ≤ val WuPaper.ClassicalFourthData.Bq 238
    have hp : val WuPaper.ClassicalFourthData.Bq 238 = (28063655608749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 238 = 28063655608749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 238 = (4119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 239) ≤ val WuPaper.ClassicalFourthData.Bq 239
    have hp : val WuPaper.ClassicalFourthData.Bq 239 = (28174793664576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 239 = 28174793664576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 239 = (8239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_014
