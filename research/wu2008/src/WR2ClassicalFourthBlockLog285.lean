import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints285
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_285 (j : Fin 16) (hj : 16*285+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*285+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*285+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4560) ≤ val WuPaper.ClassicalFourthData.Bq 4560
    have hp : val WuPaper.ClassicalFourthData.Bq 4560 = (242294850010752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4560 = 242294850010752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4560 = (157:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4561) ≤ val WuPaper.ClassicalFourthData.Bq 4561
    have hp : val WuPaper.ClassicalFourthData.Bq 4561 = (242312760016069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4561 = 242312760016069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4561 = (12561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4562) ≤ val WuPaper.ClassicalFourthData.Bq 4562
    have hp : val WuPaper.ClassicalFourthData.Bq 4562 = (242330662825303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4562 = 242330662825303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4562 = (6281:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4563) ≤ val WuPaper.ClassicalFourthData.Bq 4563
    have hp : val WuPaper.ClassicalFourthData.Bq 4563 = (242348558441190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4563 = 242348558441190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4563 = (12563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4564) ≤ val WuPaper.ClassicalFourthData.Bq 4564
    have hp : val WuPaper.ClassicalFourthData.Bq 4564 = (242366446866459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4564 = 242366446866459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4564 = (3141:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4565) ≤ val WuPaper.ClassicalFourthData.Bq 4565
    have hp : val WuPaper.ClassicalFourthData.Bq 4565 = (242384328103842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4565 = 242384328103842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4565 = (2513:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4566) ≤ val WuPaper.ClassicalFourthData.Bq 4566
    have hp : val WuPaper.ClassicalFourthData.Bq 4566 = (242402202156069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4566 = 242402202156069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4566 = (6283:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4567) ≤ val WuPaper.ClassicalFourthData.Bq 4567
    have hp : val WuPaper.ClassicalFourthData.Bq 4567 = (242420069025867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4567 = 242420069025867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4567 = (12567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4567
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4568) ≤ val WuPaper.ClassicalFourthData.Bq 4568
    have hp : val WuPaper.ClassicalFourthData.Bq 4568 = (242437928715964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4568 = 242437928715964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4568 = (1571:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4569) ≤ val WuPaper.ClassicalFourthData.Bq 4569
    have hp : val WuPaper.ClassicalFourthData.Bq 4569 = (242455781229085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4569 = 242455781229085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4569 = (12569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4570) ≤ val WuPaper.ClassicalFourthData.Bq 4570
    have hp : val WuPaper.ClassicalFourthData.Bq 4570 = (242473626567955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4570 = 242473626567955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4570 = (1257:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4571) ≤ val WuPaper.ClassicalFourthData.Bq 4571
    have hp : val WuPaper.ClassicalFourthData.Bq 4571 = (242491464735298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4571 = 242491464735298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4571 = (12571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4572) ≤ val WuPaper.ClassicalFourthData.Bq 4572
    have hp : val WuPaper.ClassicalFourthData.Bq 4572 = (242509295733834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4572 = 242509295733834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4572 = (3143:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4573) ≤ val WuPaper.ClassicalFourthData.Bq 4573
    have hp : val WuPaper.ClassicalFourthData.Bq 4573 = (242527119566286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4573 = 242527119566286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4573 = (12573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4574) ≤ val WuPaper.ClassicalFourthData.Bq 4574
    have hp : val WuPaper.ClassicalFourthData.Bq 4574 = (242544936235373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4574 = 242544936235373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4574 = (6287:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4575) ≤ val WuPaper.ClassicalFourthData.Bq 4575
    have hp : val WuPaper.ClassicalFourthData.Bq 4575 = (242562745743814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4575 = 242562745743814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4575 = (503:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_285
