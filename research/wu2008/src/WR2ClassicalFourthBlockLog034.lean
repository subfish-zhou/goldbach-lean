import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints034
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_034 (j : Fin 16) (hj : 16*34+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*34+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*34+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 544) ≤ val WuPaper.ClassicalFourthData.Bq 544
    have hp : val WuPaper.ClassicalFourthData.Bq 544 = (59697247330974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 544 = 59697247330974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 544 = (267:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 545) ≤ val WuPaper.ClassicalFourthData.Bq 545
    have hp : val WuPaper.ClassicalFourthData.Bq 545 = (59793266944203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 545 = 59793266944203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 545 = (1709:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 546) ≤ val WuPaper.ClassicalFourthData.Bq 546
    have hp : val WuPaper.ClassicalFourthData.Bq 546 = (59889241427785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 546 = 59889241427785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 546 = (4273:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 547) ≤ val WuPaper.ClassicalFourthData.Bq 547
    have hp : val WuPaper.ClassicalFourthData.Bq 547 = (59985170807527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 547 = 59985170807527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 547 = (8547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 548) ≤ val WuPaper.ClassicalFourthData.Bq 548
    have hp : val WuPaper.ClassicalFourthData.Bq 548 = (60081055109219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 548 = 60081055109219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 548 = (2137:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 549) ≤ val WuPaper.ClassicalFourthData.Bq 549
    have hp : val WuPaper.ClassicalFourthData.Bq 549 = (60176894358628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 549 = 60176894358628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 549 = (8549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 550) ≤ val WuPaper.ClassicalFourthData.Bq 550
    have hp : val WuPaper.ClassicalFourthData.Bq 550 = (60272688581506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 550 = 60272688581506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 550 = (171:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 551) ≤ val WuPaper.ClassicalFourthData.Bq 551
    have hp : val WuPaper.ClassicalFourthData.Bq 551 = (60368437803586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 551 = 60368437803586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 551 = (8551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_551
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 552) ≤ val WuPaper.ClassicalFourthData.Bq 552
    have hp : val WuPaper.ClassicalFourthData.Bq 552 = (60464142050580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 552 = 60464142050580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 552 = (1069:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 553) ≤ val WuPaper.ClassicalFourthData.Bq 553
    have hp : val WuPaper.ClassicalFourthData.Bq 553 = (60559801348184:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 553 = 60559801348184 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 553 = (8553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 554) ≤ val WuPaper.ClassicalFourthData.Bq 554
    have hp : val WuPaper.ClassicalFourthData.Bq 554 = (60655415722075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 554 = 60655415722075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 554 = (4277:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 555) ≤ val WuPaper.ClassicalFourthData.Bq 555
    have hp : val WuPaper.ClassicalFourthData.Bq 555 = (60750985197911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 555 = 60750985197911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 555 = (1711:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 556) ≤ val WuPaper.ClassicalFourthData.Bq 556
    have hp : val WuPaper.ClassicalFourthData.Bq 556 = (60846509801331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 556 = 60846509801331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 556 = (2139:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 557) ≤ val WuPaper.ClassicalFourthData.Bq 557
    have hp : val WuPaper.ClassicalFourthData.Bq 557 = (60941989557955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 557 = 60941989557955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 557 = (8557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 558) ≤ val WuPaper.ClassicalFourthData.Bq 558
    have hp : val WuPaper.ClassicalFourthData.Bq 558 = (61037424493388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 558 = 61037424493388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 558 = (4279:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 559) ≤ val WuPaper.ClassicalFourthData.Bq 559
    have hp : val WuPaper.ClassicalFourthData.Bq 559 = (61132814633212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 559 = 61132814633212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 559 = (8559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_034
