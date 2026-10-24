import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints641
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_641 (j : Fin 16) (hj : 16*641+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*641+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*641+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10256) ≤ val WuPaper.ClassicalFourthData.Bq 10256
    have hp : val WuPaper.ClassicalFourthData.Bq 10256 = (278458262434170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10256 = 278458262434170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10256 = (1141:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10257) ≤ val WuPaper.ClassicalFourthData.Bq 10257
    have hp : val WuPaper.ClassicalFourthData.Bq 10257 = (278458378308185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10257 = 278458378308185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10257 = (18257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10258) ≤ val WuPaper.ClassicalFourthData.Bq 10258
    have hp : val WuPaper.ClassicalFourthData.Bq 10258 = (278458493091677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10258 = 278458493091677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10258 = (9129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10259) ≤ val WuPaper.ClassicalFourthData.Bq 10259
    have hp : val WuPaper.ClassicalFourthData.Bq 10259 = (278458606784976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10259 = 278458606784976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10259 = (18259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10260) ≤ val WuPaper.ClassicalFourthData.Bq 10260
    have hp : val WuPaper.ClassicalFourthData.Bq 10260 = (278458719388412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10260 = 278458719388412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10260 = (913:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10261) ≤ val WuPaper.ClassicalFourthData.Bq 10261
    have hp : val WuPaper.ClassicalFourthData.Bq 10261 = (278458830902315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10261 = 278458830902315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10261 = (18261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10262) ≤ val WuPaper.ClassicalFourthData.Bq 10262
    have hp : val WuPaper.ClassicalFourthData.Bq 10262 = (278458941327015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10262 = 278458941327015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10262 = (9131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10263) ≤ val WuPaper.ClassicalFourthData.Bq 10263
    have hp : val WuPaper.ClassicalFourthData.Bq 10263 = (278459050662843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10263 = 278459050662843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10263 = (18263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10264) ≤ val WuPaper.ClassicalFourthData.Bq 10264
    have hp : val WuPaper.ClassicalFourthData.Bq 10264 = (278459158910128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10264 = 278459158910128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10264 = (2283:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10265) ≤ val WuPaper.ClassicalFourthData.Bq 10265
    have hp : val WuPaper.ClassicalFourthData.Bq 10265 = (278459266069200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10265 = 278459266069200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10265 = (3653:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10266) ≤ val WuPaper.ClassicalFourthData.Bq 10266
    have hp : val WuPaper.ClassicalFourthData.Bq 10266 = (278459372140388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10266 = 278459372140388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10266 = (9133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10267) ≤ val WuPaper.ClassicalFourthData.Bq 10267
    have hp : val WuPaper.ClassicalFourthData.Bq 10267 = (278459477124022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10267 = 278459477124022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10267 = (18267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10268) ≤ val WuPaper.ClassicalFourthData.Bq 10268
    have hp : val WuPaper.ClassicalFourthData.Bq 10268 = (278459581020432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10268 = 278459581020432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10268 = (4567:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10269) ≤ val WuPaper.ClassicalFourthData.Bq 10269
    have hp : val WuPaper.ClassicalFourthData.Bq 10269 = (278459683829946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10269 = 278459683829946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10269 = (18269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10270) ≤ val WuPaper.ClassicalFourthData.Bq 10270
    have hp : val WuPaper.ClassicalFourthData.Bq 10270 = (278459785552894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10270 = 278459785552894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10270 = (1827:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10271) ≤ val WuPaper.ClassicalFourthData.Bq 10271
    have hp : val WuPaper.ClassicalFourthData.Bq 10271 = (278459886189606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10271 = 278459886189606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10271 = (18271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_641
