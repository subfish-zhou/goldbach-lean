import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints156
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_156 (j : Fin 16) (hj : 16*156+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*156+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*156+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2496) ≤ val WuPaper.ClassicalFourthData.Bq 2496
    have hp : val WuPaper.ClassicalFourthData.Bq 2496 = (184791250662914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2496 = 184791250662914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2496 = (328:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2497) ≤ val WuPaper.ClassicalFourthData.Bq 2497
    have hp : val WuPaper.ClassicalFourthData.Bq 2497 = (184832302859295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2497 = 184832302859295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2497 = (10497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2498) ≤ val WuPaper.ClassicalFourthData.Bq 2498
    have hp : val WuPaper.ClassicalFourthData.Bq 2498 = (184873338208047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2498 = 184873338208047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2498 = (5249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2499) ≤ val WuPaper.ClassicalFourthData.Bq 2499
    have hp : val WuPaper.ClassicalFourthData.Bq 2499 = (184914356716763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2499 = 184914356716763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2499 = (10499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2500) ≤ val WuPaper.ClassicalFourthData.Bq 2500
    have hp : val WuPaper.ClassicalFourthData.Bq 2500 = (184955358393029:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2500 = 184955358393029 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2500 = (21:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2501) ≤ val WuPaper.ClassicalFourthData.Bq 2501
    have hp : val WuPaper.ClassicalFourthData.Bq 2501 = (184996343244431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2501 = 184996343244431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2501 = (10501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2502) ≤ val WuPaper.ClassicalFourthData.Bq 2502
    have hp : val WuPaper.ClassicalFourthData.Bq 2502 = (185037311278547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2502 = 185037311278547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2502 = (5251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2503) ≤ val WuPaper.ClassicalFourthData.Bq 2503
    have hp : val WuPaper.ClassicalFourthData.Bq 2503 = (185078262502952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2503 = 185078262502952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2503 = (10503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2504) ≤ val WuPaper.ClassicalFourthData.Bq 2504
    have hp : val WuPaper.ClassicalFourthData.Bq 2504 = (185119196925217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2504 = 185119196925217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2504 = (1313:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2505) ≤ val WuPaper.ClassicalFourthData.Bq 2505
    have hp : val WuPaper.ClassicalFourthData.Bq 2505 = (185160114552910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2505 = 185160114552910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2505 = (2101:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2506) ≤ val WuPaper.ClassicalFourthData.Bq 2506
    have hp : val WuPaper.ClassicalFourthData.Bq 2506 = (185201015393592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2506 = 185201015393592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2506 = (5253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2507) ≤ val WuPaper.ClassicalFourthData.Bq 2507
    have hp : val WuPaper.ClassicalFourthData.Bq 2507 = (185241899454824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2507 = 185241899454824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2507 = (10507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2508) ≤ val WuPaper.ClassicalFourthData.Bq 2508
    have hp : val WuPaper.ClassicalFourthData.Bq 2508 = (185282766744158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2508 = 185282766744158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2508 = (2627:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2509) ≤ val WuPaper.ClassicalFourthData.Bq 2509
    have hp : val WuPaper.ClassicalFourthData.Bq 2509 = (185323617269145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2509 = 185323617269145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2509 = (10509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2510) ≤ val WuPaper.ClassicalFourthData.Bq 2510
    have hp : val WuPaper.ClassicalFourthData.Bq 2510 = (185364451037332:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2510 = 185364451037332 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2510 = (1051:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2511) ≤ val WuPaper.ClassicalFourthData.Bq 2511
    have hp : val WuPaper.ClassicalFourthData.Bq 2511 = (185405268056259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2511 = 185405268056259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2511 = (10511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_156
