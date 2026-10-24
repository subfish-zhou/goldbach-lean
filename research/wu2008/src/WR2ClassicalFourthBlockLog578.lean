import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints578
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_578 (j : Fin 16) (hj : 16*578+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*578+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*578+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9248) ≤ val WuPaper.ClassicalFourthData.Bq 9248
    have hp : val WuPaper.ClassicalFourthData.Bq 9248 = (277725472298390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9248 = 277725472298390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9248 = (539:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9249) ≤ val WuPaper.ClassicalFourthData.Bq 9249
    have hp : val WuPaper.ClassicalFourthData.Bq 9249 = (277726875017401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9249 = 277726875017401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9249 = (17249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9250) ≤ val WuPaper.ClassicalFourthData.Bq 9250
    have hp : val WuPaper.ClassicalFourthData.Bq 9250 = (277728276252773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9250 = 277728276252773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9250 = (69:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9251) ≤ val WuPaper.ClassicalFourthData.Bq 9251
    have hp : val WuPaper.ClassicalFourthData.Bq 9251 = (277729676004962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9251 = 277729676004962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9251 = (17251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9252) ≤ val WuPaper.ClassicalFourthData.Bq 9252
    have hp : val WuPaper.ClassicalFourthData.Bq 9252 = (277731074274425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9252 = 277731074274425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9252 = (4313:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9253) ≤ val WuPaper.ClassicalFourthData.Bq 9253
    have hp : val WuPaper.ClassicalFourthData.Bq 9253 = (277732471061621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9253 = 277732471061621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9253 = (17253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9254) ≤ val WuPaper.ClassicalFourthData.Bq 9254
    have hp : val WuPaper.ClassicalFourthData.Bq 9254 = (277733866367006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9254 = 277733866367006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9254 = (8627:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9255) ≤ val WuPaper.ClassicalFourthData.Bq 9255
    have hp : val WuPaper.ClassicalFourthData.Bq 9255 = (277735260191036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9255 = 277735260191036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9255 = (3451:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9255
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9256) ≤ val WuPaper.ClassicalFourthData.Bq 9256
    have hp : val WuPaper.ClassicalFourthData.Bq 9256 = (277736652534168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9256 = 277736652534168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9256 = (2157:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9257) ≤ val WuPaper.ClassicalFourthData.Bq 9257
    have hp : val WuPaper.ClassicalFourthData.Bq 9257 = (277738043396860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9257 = 277738043396860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9257 = (17257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9258) ≤ val WuPaper.ClassicalFourthData.Bq 9258
    have hp : val WuPaper.ClassicalFourthData.Bq 9258 = (277739432779566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9258 = 277739432779566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9258 = (8629:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9259) ≤ val WuPaper.ClassicalFourthData.Bq 9259
    have hp : val WuPaper.ClassicalFourthData.Bq 9259 = (277740820682744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9259 = 277740820682744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9259 = (17259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9260) ≤ val WuPaper.ClassicalFourthData.Bq 9260
    have hp : val WuPaper.ClassicalFourthData.Bq 9260 = (277742207106849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9260 = 277742207106849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9260 = (863:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9261) ≤ val WuPaper.ClassicalFourthData.Bq 9261
    have hp : val WuPaper.ClassicalFourthData.Bq 9261 = (277743592052337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9261 = 277743592052337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9261 = (17261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9262) ≤ val WuPaper.ClassicalFourthData.Bq 9262
    have hp : val WuPaper.ClassicalFourthData.Bq 9262 = (277744975519664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9262 = 277744975519664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9262 = (8631:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9263) ≤ val WuPaper.ClassicalFourthData.Bq 9263
    have hp : val WuPaper.ClassicalFourthData.Bq 9263 = (277746357509285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9263 = 277746357509285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9263 = (17263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_578
