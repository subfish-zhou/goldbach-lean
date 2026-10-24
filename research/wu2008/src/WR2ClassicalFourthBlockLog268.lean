import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints268
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_268 (j : Fin 16) (hj : 16*268+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*268+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*268+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4288) ≤ val WuPaper.ClassicalFourthData.Bq 4288
    have hp : val WuPaper.ClassicalFourthData.Bq 4288 = (237146589973059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4288 = 237146589973059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4288 = (384:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4289) ≤ val WuPaper.ClassicalFourthData.Bq 4289
    have hp : val WuPaper.ClassicalFourthData.Bq 4289 = (237166563101798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4289 = 237166563101798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4289 = (12289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4290) ≤ val WuPaper.ClassicalFourthData.Bq 4290
    have hp : val WuPaper.ClassicalFourthData.Bq 4290 = (237186528243227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4290 = 237186528243227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4290 = (1229:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4291) ≤ val WuPaper.ClassicalFourthData.Bq 4291
    have hp : val WuPaper.ClassicalFourthData.Bq 4291 = (237206485400437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4291 = 237206485400437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4291 = (12291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4292) ≤ val WuPaper.ClassicalFourthData.Bq 4292
    have hp : val WuPaper.ClassicalFourthData.Bq 4292 = (237226434576519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4292 = 237226434576519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4292 = (3073:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4293) ≤ val WuPaper.ClassicalFourthData.Bq 4293
    have hp : val WuPaper.ClassicalFourthData.Bq 4293 = (237246375774564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4293 = 237246375774564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4293 = (12293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4294) ≤ val WuPaper.ClassicalFourthData.Bq 4294
    have hp : val WuPaper.ClassicalFourthData.Bq 4294 = (237266308997658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4294 = 237266308997658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4294 = (6147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4295) ≤ val WuPaper.ClassicalFourthData.Bq 4295
    have hp : val WuPaper.ClassicalFourthData.Bq 4295 = (237286234248888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4295 = 237286234248888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4295 = (2459:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4296) ≤ val WuPaper.ClassicalFourthData.Bq 4296
    have hp : val WuPaper.ClassicalFourthData.Bq 4296 = (237306151531339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4296 = 237306151531339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4296 = (1537:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4297) ≤ val WuPaper.ClassicalFourthData.Bq 4297
    have hp : val WuPaper.ClassicalFourthData.Bq 4297 = (237326060848096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4297 = 237326060848096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4297 = (12297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4298) ≤ val WuPaper.ClassicalFourthData.Bq 4298
    have hp : val WuPaper.ClassicalFourthData.Bq 4298 = (237345962202240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4298 = 237345962202240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4298 = (6149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4299) ≤ val WuPaper.ClassicalFourthData.Bq 4299
    have hp : val WuPaper.ClassicalFourthData.Bq 4299 = (237365855596852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4299 = 237365855596852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4299 = (12299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4300) ≤ val WuPaper.ClassicalFourthData.Bq 4300
    have hp : val WuPaper.ClassicalFourthData.Bq 4300 = (237385741035012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4300 = 237385741035012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4300 = (123:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4301) ≤ val WuPaper.ClassicalFourthData.Bq 4301
    have hp : val WuPaper.ClassicalFourthData.Bq 4301 = (237405618519798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4301 = 237405618519798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4301 = (12301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4302) ≤ val WuPaper.ClassicalFourthData.Bq 4302
    have hp : val WuPaper.ClassicalFourthData.Bq 4302 = (237425488054286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4302 = 237425488054286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4302 = (6151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4303) ≤ val WuPaper.ClassicalFourthData.Bq 4303
    have hp : val WuPaper.ClassicalFourthData.Bq 4303 = (237445349641552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4303 = 237445349641552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4303 = (12303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_268
