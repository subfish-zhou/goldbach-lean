import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints143
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_143 (j : Fin 16) (hj : 16*143+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*143+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*143+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2288) ≤ val WuPaper.ClassicalFourthData.Bq 2288
    have hp : val WuPaper.ClassicalFourthData.Bq 2288 = (175874297825434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2288 = 175874297825434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2288 = (643:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2289) ≤ val WuPaper.ClassicalFourthData.Bq 2289
    have hp : val WuPaper.ClassicalFourthData.Bq 2289 = (175919025927292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2289 = 175919025927292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2289 = (10289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2290) ≤ val WuPaper.ClassicalFourthData.Bq 2290
    have hp : val WuPaper.ClassicalFourthData.Bq 2290 = (175963735507273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2290 = 175963735507273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2290 = (1029:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2291) ≤ val WuPaper.ClassicalFourthData.Bq 2291
    have hp : val WuPaper.ClassicalFourthData.Bq 2291 = (176008426573901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2291 = 176008426573901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2291 = (10291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2292) ≤ val WuPaper.ClassicalFourthData.Bq 2292
    have hp : val WuPaper.ClassicalFourthData.Bq 2292 = (176053099135695:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2292 = 176053099135695 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2292 = (2573:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2293) ≤ val WuPaper.ClassicalFourthData.Bq 2293
    have hp : val WuPaper.ClassicalFourthData.Bq 2293 = (176097753201169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2293 = 176097753201169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2293 = (10293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2294) ≤ val WuPaper.ClassicalFourthData.Bq 2294
    have hp : val WuPaper.ClassicalFourthData.Bq 2294 = (176142388778833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2294 = 176142388778833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2294 = (5147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2295) ≤ val WuPaper.ClassicalFourthData.Bq 2295
    have hp : val WuPaper.ClassicalFourthData.Bq 2295 = (176187005877191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2295 = 176187005877191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2295 = (2059:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2296) ≤ val WuPaper.ClassicalFourthData.Bq 2296
    have hp : val WuPaper.ClassicalFourthData.Bq 2296 = (176231604504745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2296 = 176231604504745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2296 = (1287:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2297) ≤ val WuPaper.ClassicalFourthData.Bq 2297
    have hp : val WuPaper.ClassicalFourthData.Bq 2297 = (176276184669988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2297 = 176276184669988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2297 = (10297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2298) ≤ val WuPaper.ClassicalFourthData.Bq 2298
    have hp : val WuPaper.ClassicalFourthData.Bq 2298 = (176320746381411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2298 = 176320746381411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2298 = (5149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2299) ≤ val WuPaper.ClassicalFourthData.Bq 2299
    have hp : val WuPaper.ClassicalFourthData.Bq 2299 = (176365289647501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2299 = 176365289647501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2299 = (10299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2300) ≤ val WuPaper.ClassicalFourthData.Bq 2300
    have hp : val WuPaper.ClassicalFourthData.Bq 2300 = (176409814476737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2300 = 176409814476737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2300 = (103:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2301) ≤ val WuPaper.ClassicalFourthData.Bq 2301
    have hp : val WuPaper.ClassicalFourthData.Bq 2301 = (176454320877596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2301 = 176454320877596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2301 = (10301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2302) ≤ val WuPaper.ClassicalFourthData.Bq 2302
    have hp : val WuPaper.ClassicalFourthData.Bq 2302 = (176498808858549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2302 = 176498808858549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2302 = (5151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2303) ≤ val WuPaper.ClassicalFourthData.Bq 2303
    have hp : val WuPaper.ClassicalFourthData.Bq 2303 = (176543278428063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2303 = 176543278428063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2303 = (10303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_143
