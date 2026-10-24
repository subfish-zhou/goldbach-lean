import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints391
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_391 (j : Fin 16) (hj : 16*391+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*391+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*391+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6256) ≤ val WuPaper.ClassicalFourthData.Bq 6256
    have hp : val WuPaper.ClassicalFourthData.Bq 6256 = (264188703439523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6256 = 264188703439523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6256 = (891:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6257) ≤ val WuPaper.ClassicalFourthData.Bq 6257
    have hp : val WuPaper.ClassicalFourthData.Bq 6257 = (264197527728251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6257 = 264197527728251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6257 = (14257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6258) ≤ val WuPaper.ClassicalFourthData.Bq 6258
    have hp : val WuPaper.ClassicalFourthData.Bq 6258 = (264206348112561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6258 = 264206348112561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6258 = (7129:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6259) ≤ val WuPaper.ClassicalFourthData.Bq 6259
    have hp : val WuPaper.ClassicalFourthData.Bq 6259 = (264215164593793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6259 = 264215164593793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6259 = (14259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6260) ≤ val WuPaper.ClassicalFourthData.Bq 6260
    have hp : val WuPaper.ClassicalFourthData.Bq 6260 = (264223977173287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6260 = 264223977173287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6260 = (713:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6261) ≤ val WuPaper.ClassicalFourthData.Bq 6261
    have hp : val WuPaper.ClassicalFourthData.Bq 6261 = (264232785852386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6261 = 264232785852386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6261 = (14261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6262) ≤ val WuPaper.ClassicalFourthData.Bq 6262
    have hp : val WuPaper.ClassicalFourthData.Bq 6262 = (264241590632427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6262 = 264241590632427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6262 = (7131:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6263) ≤ val WuPaper.ClassicalFourthData.Bq 6263
    have hp : val WuPaper.ClassicalFourthData.Bq 6263 = (264250391514751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6263 = 264250391514751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6263 = (14263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6263
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6264) ≤ val WuPaper.ClassicalFourthData.Bq 6264
    have hp : val WuPaper.ClassicalFourthData.Bq 6264 = (264259188500696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6264 = 264259188500696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6264 = (1783:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6265) ≤ val WuPaper.ClassicalFourthData.Bq 6265
    have hp : val WuPaper.ClassicalFourthData.Bq 6265 = (264267981591600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6265 = 264267981591600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6265 = (2853:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6266) ≤ val WuPaper.ClassicalFourthData.Bq 6266
    have hp : val WuPaper.ClassicalFourthData.Bq 6266 = (264276770788801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6266 = 264276770788801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6266 = (7133:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6267) ≤ val WuPaper.ClassicalFourthData.Bq 6267
    have hp : val WuPaper.ClassicalFourthData.Bq 6267 = (264285556093636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6267 = 264285556093636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6267 = (14267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6268) ≤ val WuPaper.ClassicalFourthData.Bq 6268
    have hp : val WuPaper.ClassicalFourthData.Bq 6268 = (264294337507441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6268 = 264294337507441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6268 = (3567:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6269) ≤ val WuPaper.ClassicalFourthData.Bq 6269
    have hp : val WuPaper.ClassicalFourthData.Bq 6269 = (264303115031552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6269 = 264303115031552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6269 = (14269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6270) ≤ val WuPaper.ClassicalFourthData.Bq 6270
    have hp : val WuPaper.ClassicalFourthData.Bq 6270 = (264311888667306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6270 = 264311888667306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6270 = (1427:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6271) ≤ val WuPaper.ClassicalFourthData.Bq 6271
    have hp : val WuPaper.ClassicalFourthData.Bq 6271 = (264320658416037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6271 = 264320658416037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6271 = (14271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6271
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_391
