import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints219
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_219 (j : Fin 16) (hj : 16*219+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*219+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*219+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3504) ≤ val WuPaper.ClassicalFourthData.Bq 3504
    have hp : val WuPaper.ClassicalFourthData.Bq 3504 = (218755859034782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3504 = 218755859034782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3504 = (719:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3505) ≤ val WuPaper.ClassicalFourthData.Bq 3505
    have hp : val WuPaper.ClassicalFourthData.Bq 3505 = (218783173912398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3505 = 218783173912398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3505 = (2301:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3506) ≤ val WuPaper.ClassicalFourthData.Bq 3506
    have hp : val WuPaper.ClassicalFourthData.Bq 3506 = (218810477869960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3506 = 218810477869960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3506 = (5753:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3507) ≤ val WuPaper.ClassicalFourthData.Bq 3507
    have hp : val WuPaper.ClassicalFourthData.Bq 3507 = (218837770911958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3507 = 218837770911958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3507 = (11507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3508) ≤ val WuPaper.ClassicalFourthData.Bq 3508
    have hp : val WuPaper.ClassicalFourthData.Bq 3508 = (218865053042883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3508 = 218865053042883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3508 = (2877:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3509) ≤ val WuPaper.ClassicalFourthData.Bq 3509
    have hp : val WuPaper.ClassicalFourthData.Bq 3509 = (218892324267220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3509 = 218892324267220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3509 = (11509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3510) ≤ val WuPaper.ClassicalFourthData.Bq 3510
    have hp : val WuPaper.ClassicalFourthData.Bq 3510 = (218919584589454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3510 = 218919584589454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3510 = (1151:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3511) ≤ val WuPaper.ClassicalFourthData.Bq 3511
    have hp : val WuPaper.ClassicalFourthData.Bq 3511 = (218946834014068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3511 = 218946834014068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3511 = (11511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3511
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3512) ≤ val WuPaper.ClassicalFourthData.Bq 3512
    have hp : val WuPaper.ClassicalFourthData.Bq 3512 = (218974072545543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3512 = 218974072545543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3512 = (1439:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3513) ≤ val WuPaper.ClassicalFourthData.Bq 3513
    have hp : val WuPaper.ClassicalFourthData.Bq 3513 = (219001300188356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3513 = 219001300188356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3513 = (11513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3514) ≤ val WuPaper.ClassicalFourthData.Bq 3514
    have hp : val WuPaper.ClassicalFourthData.Bq 3514 = (219028516946982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3514 = 219028516946982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3514 = (5757:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3515) ≤ val WuPaper.ClassicalFourthData.Bq 3515
    have hp : val WuPaper.ClassicalFourthData.Bq 3515 = (219055722825896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3515 = 219055722825896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3515 = (2303:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3516) ≤ val WuPaper.ClassicalFourthData.Bq 3516
    have hp : val WuPaper.ClassicalFourthData.Bq 3516 = (219082917829569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3516 = 219082917829569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3516 = (2879:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3517) ≤ val WuPaper.ClassicalFourthData.Bq 3517
    have hp : val WuPaper.ClassicalFourthData.Bq 3517 = (219110101962470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3517 = 219110101962470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3517 = (11517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3518) ≤ val WuPaper.ClassicalFourthData.Bq 3518
    have hp : val WuPaper.ClassicalFourthData.Bq 3518 = (219137275229067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3518 = 219137275229067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3518 = (5759:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3519) ≤ val WuPaper.ClassicalFourthData.Bq 3519
    have hp : val WuPaper.ClassicalFourthData.Bq 3519 = (219164437633823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3519 = 219164437633823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3519 = (11519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_219
