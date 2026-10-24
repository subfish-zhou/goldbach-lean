import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints019
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_019 (j : Fin 16) (hj : 16*19+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*19+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*19+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 304) ≤ val WuPaper.ClassicalFourthData.Bq 304
    have hp : val WuPaper.ClassicalFourthData.Bq 304 = (35284422803273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 304 = 35284422803273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 304 = (519:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 305) ≤ val WuPaper.ClassicalFourthData.Bq 305
    have hp : val WuPaper.ClassicalFourthData.Bq 305 = (35392065868660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 305 = 35392065868660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 305 = (1661:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 306) ≤ val WuPaper.ClassicalFourthData.Bq 306
    have hp : val WuPaper.ClassicalFourthData.Bq 306 = (35499657029753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 306 = 35499657029753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 306 = (4153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 307) ≤ val WuPaper.ClassicalFourthData.Bq 307
    have hp : val WuPaper.ClassicalFourthData.Bq 307 = (35607196317363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 307 = 35607196317363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 307 = (8307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 308) ≤ val WuPaper.ClassicalFourthData.Bq 308
    have hp : val WuPaper.ClassicalFourthData.Bq 308 = (35714683762279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 308 = 35714683762279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 308 = (2077:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 309) ≤ val WuPaper.ClassicalFourthData.Bq 309
    have hp : val WuPaper.ClassicalFourthData.Bq 309 = (35822119395264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 309 = 35822119395264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 309 = (8309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 310) ≤ val WuPaper.ClassicalFourthData.Bq 310
    have hp : val WuPaper.ClassicalFourthData.Bq 310 = (35929503247060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 310 = 35929503247060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 310 = (831:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 311) ≤ val WuPaper.ClassicalFourthData.Bq 311
    have hp : val WuPaper.ClassicalFourthData.Bq 311 = (36036835348386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 311 = 36036835348386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 311 = (8311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 312) ≤ val WuPaper.ClassicalFourthData.Bq 312
    have hp : val WuPaper.ClassicalFourthData.Bq 312 = (36144115729936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 312 = 36144115729936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 312 = (1039:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 313) ≤ val WuPaper.ClassicalFourthData.Bq 313
    have hp : val WuPaper.ClassicalFourthData.Bq 313 = (36251344422383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 313 = 36251344422383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 313 = (8313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 314) ≤ val WuPaper.ClassicalFourthData.Bq 314
    have hp : val WuPaper.ClassicalFourthData.Bq 314 = (36358521456375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 314 = 36358521456375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 314 = (4157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 315) ≤ val WuPaper.ClassicalFourthData.Bq 315
    have hp : val WuPaper.ClassicalFourthData.Bq 315 = (36465646862538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 315 = 36465646862538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 315 = (1663:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 316) ≤ val WuPaper.ClassicalFourthData.Bq 316
    have hp : val WuPaper.ClassicalFourthData.Bq 316 = (36572720671476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 316 = 36572720671476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 316 = (2079:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 317) ≤ val WuPaper.ClassicalFourthData.Bq 317
    have hp : val WuPaper.ClassicalFourthData.Bq 317 = (36679742913767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 317 = 36679742913767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 317 = (8317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 318) ≤ val WuPaper.ClassicalFourthData.Bq 318
    have hp : val WuPaper.ClassicalFourthData.Bq 318 = (36786713619969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 318 = 36786713619969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 318 = (4159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 319) ≤ val WuPaper.ClassicalFourthData.Bq 319
    have hp : val WuPaper.ClassicalFourthData.Bq 319 = (36893632820615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 319 = 36893632820615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 319 = (8319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_019
