import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints160
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_160 (j : Fin 16) (hj : 16*160+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*160+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*160+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2560) ≤ val WuPaper.ClassicalFourthData.Bq 2560
    have hp : val WuPaper.ClassicalFourthData.Bq 2560 = (187384940089435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2560 = 187384940089435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2560 = (66:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2561) ≤ val WuPaper.ClassicalFourthData.Bq 2561
    have hp : val WuPaper.ClassicalFourthData.Bq 2561 = (187424929170666:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2561 = 187424929170666 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2561 = (10561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2562) ≤ val WuPaper.ClassicalFourthData.Bq 2562
    have hp : val WuPaper.ClassicalFourthData.Bq 2562 = (187464901881848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2562 = 187464901881848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2562 = (5281:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2563) ≤ val WuPaper.ClassicalFourthData.Bq 2563
    have hp : val WuPaper.ClassicalFourthData.Bq 2563 = (187504858230312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2563 = 187504858230312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2563 = (10563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2564) ≤ val WuPaper.ClassicalFourthData.Bq 2564
    have hp : val WuPaper.ClassicalFourthData.Bq 2564 = (187544798223383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2564 = 187544798223383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2564 = (2641:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2565) ≤ val WuPaper.ClassicalFourthData.Bq 2565
    have hp : val WuPaper.ClassicalFourthData.Bq 2565 = (187584721868384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2565 = 187584721868384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2565 = (2113:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2566) ≤ val WuPaper.ClassicalFourthData.Bq 2566
    have hp : val WuPaper.ClassicalFourthData.Bq 2566 = (187624629172634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2566 = 187624629172634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2566 = (5283:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2567) ≤ val WuPaper.ClassicalFourthData.Bq 2567
    have hp : val WuPaper.ClassicalFourthData.Bq 2567 = (187664520143445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2567 = 187664520143445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2567 = (10567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2567
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2568) ≤ val WuPaper.ClassicalFourthData.Bq 2568
    have hp : val WuPaper.ClassicalFourthData.Bq 2568 = (187704394788129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2568 = 187704394788129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2568 = (1321:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2568
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2569) ≤ val WuPaper.ClassicalFourthData.Bq 2569
    have hp : val WuPaper.ClassicalFourthData.Bq 2569 = (187744253113992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2569 = 187744253113992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2569 = (10569:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2569
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2570) ≤ val WuPaper.ClassicalFourthData.Bq 2570
    have hp : val WuPaper.ClassicalFourthData.Bq 2570 = (187784095128337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2570 = 187784095128337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2570 = (1057:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2570
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2571) ≤ val WuPaper.ClassicalFourthData.Bq 2571
    have hp : val WuPaper.ClassicalFourthData.Bq 2571 = (187823920838461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2571 = 187823920838461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2571 = (10571:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2571
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2572) ≤ val WuPaper.ClassicalFourthData.Bq 2572
    have hp : val WuPaper.ClassicalFourthData.Bq 2572 = (187863730251658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2572 = 187863730251658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2572 = (2643:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2572
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2573) ≤ val WuPaper.ClassicalFourthData.Bq 2573
    have hp : val WuPaper.ClassicalFourthData.Bq 2573 = (187903523375220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2573 = 187903523375220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2573 = (10573:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2573
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2574) ≤ val WuPaper.ClassicalFourthData.Bq 2574
    have hp : val WuPaper.ClassicalFourthData.Bq 2574 = (187943300216432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2574 = 187943300216432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2574 = (5287:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2574
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2575) ≤ val WuPaper.ClassicalFourthData.Bq 2575
    have hp : val WuPaper.ClassicalFourthData.Bq 2575 = (187983060782577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2575 = 187983060782577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2575 = (423:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2575
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_160
