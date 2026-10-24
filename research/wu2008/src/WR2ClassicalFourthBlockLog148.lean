import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints148
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_148 (j : Fin 16) (hj : 16*148+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*148+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*148+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2368) ≤ val WuPaper.ClassicalFourthData.Bq 2368
    have hp : val WuPaper.ClassicalFourthData.Bq 2368 = (179394709653624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2368 = 179394709653624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2368 = (324:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2369) ≤ val WuPaper.ClassicalFourthData.Bq 2369
    have hp : val WuPaper.ClassicalFourthData.Bq 2369 = (179437982551582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2369 = 179437982551582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2369 = (10369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2370) ≤ val WuPaper.ClassicalFourthData.Bq 2370
    have hp : val WuPaper.ClassicalFourthData.Bq 2370 = (179481237594670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2370 = 179481237594670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2370 = (1037:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2371) ≤ val WuPaper.ClassicalFourthData.Bq 2371
    have hp : val WuPaper.ClassicalFourthData.Bq 2371 = (179524474791037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2371 = 179524474791037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2371 = (10371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2372) ≤ val WuPaper.ClassicalFourthData.Bq 2372
    have hp : val WuPaper.ClassicalFourthData.Bq 2372 = (179567694148829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2372 = 179567694148829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2372 = (2593:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2373) ≤ val WuPaper.ClassicalFourthData.Bq 2373
    have hp : val WuPaper.ClassicalFourthData.Bq 2373 = (179610895676185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2373 = 179610895676185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2373 = (10373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2374) ≤ val WuPaper.ClassicalFourthData.Bq 2374
    have hp : val WuPaper.ClassicalFourthData.Bq 2374 = (179654079381244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2374 = 179654079381244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2374 = (5187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2375) ≤ val WuPaper.ClassicalFourthData.Bq 2375
    have hp : val WuPaper.ClassicalFourthData.Bq 2375 = (179697245272135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2375 = 179697245272135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2375 = (83:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2376) ≤ val WuPaper.ClassicalFourthData.Bq 2376
    have hp : val WuPaper.ClassicalFourthData.Bq 2376 = (179740393356987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2376 = 179740393356987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2376 = (1297:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2377) ≤ val WuPaper.ClassicalFourthData.Bq 2377
    have hp : val WuPaper.ClassicalFourthData.Bq 2377 = (179783523643922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2377 = 179783523643922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2377 = (10377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2378) ≤ val WuPaper.ClassicalFourthData.Bq 2378
    have hp : val WuPaper.ClassicalFourthData.Bq 2378 = (179826636141059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2378 = 179826636141059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2378 = (5189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2379) ≤ val WuPaper.ClassicalFourthData.Bq 2379
    have hp : val WuPaper.ClassicalFourthData.Bq 2379 = (179869730856510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2379 = 179869730856510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2379 = (10379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2380) ≤ val WuPaper.ClassicalFourthData.Bq 2380
    have hp : val WuPaper.ClassicalFourthData.Bq 2380 = (179912807798385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2380 = 179912807798385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2380 = (519:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2381) ≤ val WuPaper.ClassicalFourthData.Bq 2381
    have hp : val WuPaper.ClassicalFourthData.Bq 2381 = (179955866974789:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2381 = 179955866974789 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2381 = (10381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2382) ≤ val WuPaper.ClassicalFourthData.Bq 2382
    have hp : val WuPaper.ClassicalFourthData.Bq 2382 = (179998908393821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2382 = 179998908393821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2382 = (5191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2383) ≤ val WuPaper.ClassicalFourthData.Bq 2383
    have hp : val WuPaper.ClassicalFourthData.Bq 2383 = (180041932063577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2383 = 180041932063577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2383 = (10383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_148
