import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints389
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_389 (j : Fin 16) (hj : 16*389+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*389+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*389+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6224) ≤ val WuPaper.ClassicalFourthData.Bq 6224
    have hp : val WuPaper.ClassicalFourthData.Bq 6224 = (263904256612858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6224 = 263904256612858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6224 = (889:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6225) ≤ val WuPaper.ClassicalFourthData.Bq 6225
    have hp : val WuPaper.ClassicalFourthData.Bq 6225 = (263913206554378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6225 = 263913206554378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6225 = (569:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6226) ≤ val WuPaper.ClassicalFourthData.Bq 6226
    have hp : val WuPaper.ClassicalFourthData.Bq 6226 = (263922152548278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6226 = 263922152548278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6226 = (7113:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6227) ≤ val WuPaper.ClassicalFourthData.Bq 6227
    have hp : val WuPaper.ClassicalFourthData.Bq 6227 = (263931094595914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6227 = 263931094595914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6227 = (14227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6228) ≤ val WuPaper.ClassicalFourthData.Bq 6228
    have hp : val WuPaper.ClassicalFourthData.Bq 6228 = (263940032698646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6228 = 263940032698646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6228 = (3557:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6229) ≤ val WuPaper.ClassicalFourthData.Bq 6229
    have hp : val WuPaper.ClassicalFourthData.Bq 6229 = (263948966857829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6229 = 263948966857829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6229 = (14229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6230) ≤ val WuPaper.ClassicalFourthData.Bq 6230
    have hp : val WuPaper.ClassicalFourthData.Bq 6230 = (263957897074822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6230 = 263957897074822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6230 = (1423:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6231) ≤ val WuPaper.ClassicalFourthData.Bq 6231
    have hp : val WuPaper.ClassicalFourthData.Bq 6231 = (263966823350979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6231 = 263966823350979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6231 = (14231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6231
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6232) ≤ val WuPaper.ClassicalFourthData.Bq 6232
    have hp : val WuPaper.ClassicalFourthData.Bq 6232 = (263975745687657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6232 = 263975745687657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6232 = (1779:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6233) ≤ val WuPaper.ClassicalFourthData.Bq 6233
    have hp : val WuPaper.ClassicalFourthData.Bq 6233 = (263984664086211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6233 = 263984664086211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6233 = (14233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6234) ≤ val WuPaper.ClassicalFourthData.Bq 6234
    have hp : val WuPaper.ClassicalFourthData.Bq 6234 = (263993578547996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6234 = 263993578547996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6234 = (7117:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6235) ≤ val WuPaper.ClassicalFourthData.Bq 6235
    have hp : val WuPaper.ClassicalFourthData.Bq 6235 = (264002489074365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6235 = 264002489074365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6235 = (2847:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6236) ≤ val WuPaper.ClassicalFourthData.Bq 6236
    have hp : val WuPaper.ClassicalFourthData.Bq 6236 = (264011395666672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6236 = 264011395666672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6236 = (3559:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6237) ≤ val WuPaper.ClassicalFourthData.Bq 6237
    have hp : val WuPaper.ClassicalFourthData.Bq 6237 = (264020298326270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6237 = 264020298326270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6237 = (14237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6238) ≤ val WuPaper.ClassicalFourthData.Bq 6238
    have hp : val WuPaper.ClassicalFourthData.Bq 6238 = (264029197054512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6238 = 264029197054512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6238 = (7119:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6239) ≤ val WuPaper.ClassicalFourthData.Bq 6239
    have hp : val WuPaper.ClassicalFourthData.Bq 6239 = (264038091852749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6239 = 264038091852749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6239 = (14239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6239
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_389
