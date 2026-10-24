import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints158
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_158 (j : Fin 16) (hj : 16*158+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*158+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*158+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2528) ≤ val WuPaper.ClassicalFourthData.Bq 2528
    have hp : val WuPaper.ClassicalFourthData.Bq 2528 = (186096602029604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2528 = 186096602029604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2528 = (329:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2529) ≤ val WuPaper.ClassicalFourthData.Bq 2529
    have hp : val WuPaper.ClassicalFourthData.Bq 2529 = (186137118846845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2529 = 186137118846845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2529 = (10529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2530) ≤ val WuPaper.ClassicalFourthData.Bq 2530
    have hp : val WuPaper.ClassicalFourthData.Bq 2530 = (186177619057341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2530 = 186177619057341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2530 = (1053:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2531) ≤ val WuPaper.ClassicalFourthData.Bq 2531
    have hp : val WuPaper.ClassicalFourthData.Bq 2531 = (186218102668552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2531 = 186218102668552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2531 = (10531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2532) ≤ val WuPaper.ClassicalFourthData.Bq 2532
    have hp : val WuPaper.ClassicalFourthData.Bq 2532 = (186258569687934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2532 = 186258569687934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2532 = (2633:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2533) ≤ val WuPaper.ClassicalFourthData.Bq 2533
    have hp : val WuPaper.ClassicalFourthData.Bq 2533 = (186299020122937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2533 = 186299020122937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2533 = (10533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2534) ≤ val WuPaper.ClassicalFourthData.Bq 2534
    have hp : val WuPaper.ClassicalFourthData.Bq 2534 = (186339453981010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2534 = 186339453981010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2534 = (5267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2535) ≤ val WuPaper.ClassicalFourthData.Bq 2535
    have hp : val WuPaper.ClassicalFourthData.Bq 2535 = (186379871269595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2535 = 186379871269595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2535 = (2107:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2536) ≤ val WuPaper.ClassicalFourthData.Bq 2536
    have hp : val WuPaper.ClassicalFourthData.Bq 2536 = (186420271996132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2536 = 186420271996132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2536 = (1317:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2537) ≤ val WuPaper.ClassicalFourthData.Bq 2537
    have hp : val WuPaper.ClassicalFourthData.Bq 2537 = (186460656168057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2537 = 186460656168057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2537 = (10537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2538) ≤ val WuPaper.ClassicalFourthData.Bq 2538
    have hp : val WuPaper.ClassicalFourthData.Bq 2538 = (186501023792799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2538 = 186501023792799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2538 = (5269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2539) ≤ val WuPaper.ClassicalFourthData.Bq 2539
    have hp : val WuPaper.ClassicalFourthData.Bq 2539 = (186541374877787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2539 = 186541374877787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2539 = (10539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2540) ≤ val WuPaper.ClassicalFourthData.Bq 2540
    have hp : val WuPaper.ClassicalFourthData.Bq 2540 = (186581709430443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2540 = 186581709430443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2540 = (527:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2541) ≤ val WuPaper.ClassicalFourthData.Bq 2541
    have hp : val WuPaper.ClassicalFourthData.Bq 2541 = (186622027458187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2541 = 186622027458187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2541 = (10541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2542) ≤ val WuPaper.ClassicalFourthData.Bq 2542
    have hp : val WuPaper.ClassicalFourthData.Bq 2542 = (186662328968432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2542 = 186662328968432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2542 = (5271:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2543) ≤ val WuPaper.ClassicalFourthData.Bq 2543
    have hp : val WuPaper.ClassicalFourthData.Bq 2543 = (186702613968590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2543 = 186702613968590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2543 = (10543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_158
