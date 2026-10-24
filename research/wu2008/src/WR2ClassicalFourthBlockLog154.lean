import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints154
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_154 (j : Fin 16) (hj : 16*154+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*154+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*154+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2464) ≤ val WuPaper.ClassicalFourthData.Bq 2464
    have hp : val WuPaper.ClassicalFourthData.Bq 2464 = (183468639181539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2464 = 183468639181539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2464 = (327:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2465) ≤ val WuPaper.ClassicalFourthData.Bq 2465
    have hp : val WuPaper.ClassicalFourthData.Bq 2465 = (183510234535664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2465 = 183510234535664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2465 = (2093:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2466) ≤ val WuPaper.ClassicalFourthData.Bq 2466
    have hp : val WuPaper.ClassicalFourthData.Bq 2466 = (183551812797001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2466 = 183551812797001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2466 = (5233:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2467) ≤ val WuPaper.ClassicalFourthData.Bq 2467
    have hp : val WuPaper.ClassicalFourthData.Bq 2467 = (183593373973275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2467 = 183593373973275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2467 = (10467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2468) ≤ val WuPaper.ClassicalFourthData.Bq 2468
    have hp : val WuPaper.ClassicalFourthData.Bq 2468 = (183634918072209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2468 = 183634918072209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2468 = (2617:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2469) ≤ val WuPaper.ClassicalFourthData.Bq 2469
    have hp : val WuPaper.ClassicalFourthData.Bq 2469 = (183676445101522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2469 = 183676445101522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2469 = (10469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2470) ≤ val WuPaper.ClassicalFourthData.Bq 2470
    have hp : val WuPaper.ClassicalFourthData.Bq 2470 = (183717955068928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2470 = 183717955068928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2470 = (1047:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2471) ≤ val WuPaper.ClassicalFourthData.Bq 2471
    have hp : val WuPaper.ClassicalFourthData.Bq 2471 = (183759447982137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2471 = 183759447982137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2471 = (10471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2471
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2472) ≤ val WuPaper.ClassicalFourthData.Bq 2472
    have hp : val WuPaper.ClassicalFourthData.Bq 2472 = (183800923848855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2472 = 183800923848855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2472 = (1309:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2473) ≤ val WuPaper.ClassicalFourthData.Bq 2473
    have hp : val WuPaper.ClassicalFourthData.Bq 2473 = (183842382676782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2473 = 183842382676782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2473 = (10473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2474) ≤ val WuPaper.ClassicalFourthData.Bq 2474
    have hp : val WuPaper.ClassicalFourthData.Bq 2474 = (183883824473616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2474 = 183883824473616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2474 = (5237:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2475) ≤ val WuPaper.ClassicalFourthData.Bq 2475
    have hp : val WuPaper.ClassicalFourthData.Bq 2475 = (183925249247050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2475 = 183925249247050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2475 = (419:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2476) ≤ val WuPaper.ClassicalFourthData.Bq 2476
    have hp : val WuPaper.ClassicalFourthData.Bq 2476 = (183966657004773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2476 = 183966657004773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2476 = (2619:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2477) ≤ val WuPaper.ClassicalFourthData.Bq 2477
    have hp : val WuPaper.ClassicalFourthData.Bq 2477 = (184008047754468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2477 = 184008047754468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2477 = (10477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2478) ≤ val WuPaper.ClassicalFourthData.Bq 2478
    have hp : val WuPaper.ClassicalFourthData.Bq 2478 = (184049421503817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2478 = 184049421503817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2478 = (5239:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2479) ≤ val WuPaper.ClassicalFourthData.Bq 2479
    have hp : val WuPaper.ClassicalFourthData.Bq 2479 = (184090778260495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2479 = 184090778260495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2479 = (10479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2479
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_154
