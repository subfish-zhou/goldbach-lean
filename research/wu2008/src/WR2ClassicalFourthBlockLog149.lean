import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints149
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_149 (j : Fin 16) (hj : 16*149+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*149+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*149+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2384) ≤ val WuPaper.ClassicalFourthData.Bq 2384
    have hp : val WuPaper.ClassicalFourthData.Bq 2384 = (180084937992149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2384 = 180084937992149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2384 = (649:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2385) ≤ val WuPaper.ClassicalFourthData.Bq 2385
    have hp : val WuPaper.ClassicalFourthData.Bq 2385 = (180127926187622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2385 = 180127926187622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2385 = (2077:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2386) ≤ val WuPaper.ClassicalFourthData.Bq 2386
    have hp : val WuPaper.ClassicalFourthData.Bq 2386 = (180170896658079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2386 = 180170896658079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2386 = (5193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2387) ≤ val WuPaper.ClassicalFourthData.Bq 2387
    have hp : val WuPaper.ClassicalFourthData.Bq 2387 = (180213849411596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2387 = 180213849411596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2387 = (10387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2388) ≤ val WuPaper.ClassicalFourthData.Bq 2388
    have hp : val WuPaper.ClassicalFourthData.Bq 2388 = (180256784456248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2388 = 180256784456248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2388 = (2597:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2389) ≤ val WuPaper.ClassicalFourthData.Bq 2389
    have hp : val WuPaper.ClassicalFourthData.Bq 2389 = (180299701800103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2389 = 180299701800103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2389 = (10389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2390) ≤ val WuPaper.ClassicalFourthData.Bq 2390
    have hp : val WuPaper.ClassicalFourthData.Bq 2390 = (180342601451224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2390 = 180342601451224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2390 = (1039:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2391) ≤ val WuPaper.ClassicalFourthData.Bq 2391
    have hp : val WuPaper.ClassicalFourthData.Bq 2391 = (180385483417671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2391 = 180385483417671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2391 = (10391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2392) ≤ val WuPaper.ClassicalFourthData.Bq 2392
    have hp : val WuPaper.ClassicalFourthData.Bq 2392 = (180428347707500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2392 = 180428347707500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2392 = (1299:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2393) ≤ val WuPaper.ClassicalFourthData.Bq 2393
    have hp : val WuPaper.ClassicalFourthData.Bq 2393 = (180471194328760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2393 = 180471194328760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2393 = (10393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2394) ≤ val WuPaper.ClassicalFourthData.Bq 2394
    have hp : val WuPaper.ClassicalFourthData.Bq 2394 = (180514023289498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2394 = 180514023289498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2394 = (5197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2395) ≤ val WuPaper.ClassicalFourthData.Bq 2395
    have hp : val WuPaper.ClassicalFourthData.Bq 2395 = (180556834597755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2395 = 180556834597755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2395 = (2079:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2396) ≤ val WuPaper.ClassicalFourthData.Bq 2396
    have hp : val WuPaper.ClassicalFourthData.Bq 2396 = (180599628261569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2396 = 180599628261569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2396 = (2599:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2397) ≤ val WuPaper.ClassicalFourthData.Bq 2397
    have hp : val WuPaper.ClassicalFourthData.Bq 2397 = (180642404288972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2397 = 180642404288972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2397 = (10397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2398) ≤ val WuPaper.ClassicalFourthData.Bq 2398
    have hp : val WuPaper.ClassicalFourthData.Bq 2398 = (180685162687993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2398 = 180685162687993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2398 = (5199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2399) ≤ val WuPaper.ClassicalFourthData.Bq 2399
    have hp : val WuPaper.ClassicalFourthData.Bq 2399 = (180727903466654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2399 = 180727903466654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2399 = (10399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_149
