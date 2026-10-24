import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints037
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_037 (j : Fin 16) (hj : 16*37+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*37+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*37+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 592) ≤ val WuPaper.ClassicalFourthData.Bq 592
    have hp : val WuPaper.ClassicalFourthData.Bq 592 = (64255725278108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 592 = 64255725278108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 592 = (537:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 593) ≤ val WuPaper.ClassicalFourthData.Bq 593
    have hp : val WuPaper.ClassicalFourthData.Bq 593 = (64349607458986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 593 = 64349607458986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 593 = (8593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 594) ≤ val WuPaper.ClassicalFourthData.Bq 594
    have hp : val WuPaper.ClassicalFourthData.Bq 594 = (64443445728190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 594 = 64443445728190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 594 = (4297:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 595) ≤ val WuPaper.ClassicalFourthData.Bq 595
    have hp : val WuPaper.ClassicalFourthData.Bq 595 = (64537240110651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 595 = 64537240110651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 595 = (1719:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 596) ≤ val WuPaper.ClassicalFourthData.Bq 596
    have hp : val WuPaper.ClassicalFourthData.Bq 596 = (64630990631280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 596 = 64630990631280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 596 = (2149:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 597) ≤ val WuPaper.ClassicalFourthData.Bq 597
    have hp : val WuPaper.ClassicalFourthData.Bq 597 = (64724697314971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 597 = 64724697314971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 597 = (8597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 598) ≤ val WuPaper.ClassicalFourthData.Bq 598
    have hp : val WuPaper.ClassicalFourthData.Bq 598 = (64818360186602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 598 = 64818360186602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 598 = (4299:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 599) ≤ val WuPaper.ClassicalFourthData.Bq 599
    have hp : val WuPaper.ClassicalFourthData.Bq 599 = (64911979271030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 599 = 64911979271030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 599 = (8599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_599
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 600) ≤ val WuPaper.ClassicalFourthData.Bq 600
    have hp : val WuPaper.ClassicalFourthData.Bq 600 = (65005554593098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 600 = 65005554593098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 600 = (43:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 601) ≤ val WuPaper.ClassicalFourthData.Bq 601
    have hp : val WuPaper.ClassicalFourthData.Bq 601 = (65099086177627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 601 = 65099086177627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 601 = (8601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 602) ≤ val WuPaper.ClassicalFourthData.Bq 602
    have hp : val WuPaper.ClassicalFourthData.Bq 602 = (65192574049423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 602 = 65192574049423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 602 = (4301:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 603) ≤ val WuPaper.ClassicalFourthData.Bq 603
    have hp : val WuPaper.ClassicalFourthData.Bq 603 = (65286018233274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 603 = 65286018233274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 603 = (8603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 604) ≤ val WuPaper.ClassicalFourthData.Bq 604
    have hp : val WuPaper.ClassicalFourthData.Bq 604 = (65379418753950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 604 = 65379418753950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 604 = (2151:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 605) ≤ val WuPaper.ClassicalFourthData.Bq 605
    have hp : val WuPaper.ClassicalFourthData.Bq 605 = (65472775636202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 605 = 65472775636202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 605 = (1721:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 606) ≤ val WuPaper.ClassicalFourthData.Bq 606
    have hp : val WuPaper.ClassicalFourthData.Bq 606 = (65566088904766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 606 = 65566088904766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 606 = (4303:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 607) ≤ val WuPaper.ClassicalFourthData.Bq 607
    have hp : val WuPaper.ClassicalFourthData.Bq 607 = (65659358584357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 607 = 65659358584357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 607 = (8607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_037
