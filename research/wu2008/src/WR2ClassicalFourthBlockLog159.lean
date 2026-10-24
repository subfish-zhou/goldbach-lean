import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints159
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_159 (j : Fin 16) (hj : 16*159+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*159+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*159+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2544) ≤ val WuPaper.ClassicalFourthData.Bq 2544
    have hp : val WuPaper.ClassicalFourthData.Bq 2544 = (186742882466069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2544 = 186742882466069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2544 = (659:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2545) ≤ val WuPaper.ClassicalFourthData.Bq 2545
    have hp : val WuPaper.ClassicalFourthData.Bq 2545 = (186783134468269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2545 = 186783134468269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2545 = (2109:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2546) ≤ val WuPaper.ClassicalFourthData.Bq 2546
    have hp : val WuPaper.ClassicalFourthData.Bq 2546 = (186823369982590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2546 = 186823369982590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2546 = (5273:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2547) ≤ val WuPaper.ClassicalFourthData.Bq 2547
    have hp : val WuPaper.ClassicalFourthData.Bq 2547 = (186863589016427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2547 = 186863589016427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2547 = (10547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2548) ≤ val WuPaper.ClassicalFourthData.Bq 2548
    have hp : val WuPaper.ClassicalFourthData.Bq 2548 = (186903791577171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2548 = 186903791577171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2548 = (2637:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2549) ≤ val WuPaper.ClassicalFourthData.Bq 2549
    have hp : val WuPaper.ClassicalFourthData.Bq 2549 = (186943977672207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2549 = 186943977672207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2549 = (10549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2550) ≤ val WuPaper.ClassicalFourthData.Bq 2550
    have hp : val WuPaper.ClassicalFourthData.Bq 2550 = (186984147308918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2550 = 186984147308918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2550 = (211:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2551) ≤ val WuPaper.ClassicalFourthData.Bq 2551
    have hp : val WuPaper.ClassicalFourthData.Bq 2551 = (187024300494683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2551 = 187024300494683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2551 = (10551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2551
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2552) ≤ val WuPaper.ClassicalFourthData.Bq 2552
    have hp : val WuPaper.ClassicalFourthData.Bq 2552 = (187064437236876:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2552 = 187064437236876 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2552 = (1319:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2553) ≤ val WuPaper.ClassicalFourthData.Bq 2553
    have hp : val WuPaper.ClassicalFourthData.Bq 2553 = (187104557542868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2553 = 187104557542868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2553 = (10553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2554) ≤ val WuPaper.ClassicalFourthData.Bq 2554
    have hp : val WuPaper.ClassicalFourthData.Bq 2554 = (187144661420024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2554 = 187144661420024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2554 = (5277:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2555) ≤ val WuPaper.ClassicalFourthData.Bq 2555
    have hp : val WuPaper.ClassicalFourthData.Bq 2555 = (187184748875708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2555 = 187184748875708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2555 = (2111:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2556) ≤ val WuPaper.ClassicalFourthData.Bq 2556
    have hp : val WuPaper.ClassicalFourthData.Bq 2556 = (187224819917277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2556 = 187224819917277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2556 = (2639:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2557) ≤ val WuPaper.ClassicalFourthData.Bq 2557
    have hp : val WuPaper.ClassicalFourthData.Bq 2557 = (187264874552086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2557 = 187264874552086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2557 = (10557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2558) ≤ val WuPaper.ClassicalFourthData.Bq 2558
    have hp : val WuPaper.ClassicalFourthData.Bq 2558 = (187304912787485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2558 = 187304912787485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2558 = (5279:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2559) ≤ val WuPaper.ClassicalFourthData.Bq 2559
    have hp : val WuPaper.ClassicalFourthData.Bq 2559 = (187344934630821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2559 = 187344934630821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2559 = (10559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_159
