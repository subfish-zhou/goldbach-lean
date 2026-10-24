import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints392
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_392 (j : Fin 16) (hj : 16*392+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*392+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*392+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6272) ≤ val WuPaper.ClassicalFourthData.Bq 6272
    have hp : val WuPaper.ClassicalFourthData.Bq 6272 = (264329424279079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6272 = 264329424279079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6272 = (446:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6273) ≤ val WuPaper.ClassicalFourthData.Bq 6273
    have hp : val WuPaper.ClassicalFourthData.Bq 6273 = (264338186257766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6273 = 264338186257766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6273 = (14273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6274) ≤ val WuPaper.ClassicalFourthData.Bq 6274
    have hp : val WuPaper.ClassicalFourthData.Bq 6274 = (264346944353432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6274 = 264346944353432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6274 = (7137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6275) ≤ val WuPaper.ClassicalFourthData.Bq 6275
    have hp : val WuPaper.ClassicalFourthData.Bq 6275 = (264355698567410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6275 = 264355698567410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6275 = (571:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6276) ≤ val WuPaper.ClassicalFourthData.Bq 6276
    have hp : val WuPaper.ClassicalFourthData.Bq 6276 = (264364448901033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6276 = 264364448901033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6276 = (3569:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6277) ≤ val WuPaper.ClassicalFourthData.Bq 6277
    have hp : val WuPaper.ClassicalFourthData.Bq 6277 = (264373195355630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6277 = 264373195355630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6277 = (14277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6278) ≤ val WuPaper.ClassicalFourthData.Bq 6278
    have hp : val WuPaper.ClassicalFourthData.Bq 6278 = (264381937932536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6278 = 264381937932536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6278 = (7139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6279) ≤ val WuPaper.ClassicalFourthData.Bq 6279
    have hp : val WuPaper.ClassicalFourthData.Bq 6279 = (264390676633079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6279 = 264390676633079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6279 = (14279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6280) ≤ val WuPaper.ClassicalFourthData.Bq 6280
    have hp : val WuPaper.ClassicalFourthData.Bq 6280 = (264399411458590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6280 = 264399411458590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6280 = (357:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6281) ≤ val WuPaper.ClassicalFourthData.Bq 6281
    have hp : val WuPaper.ClassicalFourthData.Bq 6281 = (264408142410400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6281 = 264408142410400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6281 = (14281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6282) ≤ val WuPaper.ClassicalFourthData.Bq 6282
    have hp : val WuPaper.ClassicalFourthData.Bq 6282 = (264416869489837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6282 = 264416869489837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6282 = (7141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6283) ≤ val WuPaper.ClassicalFourthData.Bq 6283
    have hp : val WuPaper.ClassicalFourthData.Bq 6283 = (264425592698229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6283 = 264425592698229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6283 = (14283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6284) ≤ val WuPaper.ClassicalFourthData.Bq 6284
    have hp : val WuPaper.ClassicalFourthData.Bq 6284 = (264434312036906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6284 = 264434312036906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6284 = (3571:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6285) ≤ val WuPaper.ClassicalFourthData.Bq 6285
    have hp : val WuPaper.ClassicalFourthData.Bq 6285 = (264443027507195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6285 = 264443027507195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6285 = (2857:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6286) ≤ val WuPaper.ClassicalFourthData.Bq 6286
    have hp : val WuPaper.ClassicalFourthData.Bq 6286 = (264451739110422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6286 = 264451739110422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6286 = (7143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6287) ≤ val WuPaper.ClassicalFourthData.Bq 6287
    have hp : val WuPaper.ClassicalFourthData.Bq 6287 = (264460446847915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6287 = 264460446847915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6287 = (14287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_392
