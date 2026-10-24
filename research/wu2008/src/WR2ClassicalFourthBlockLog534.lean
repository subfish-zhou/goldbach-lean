import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints534
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_534 (j : Fin 16) (hj : 16*534+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*534+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*534+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8544) ≤ val WuPaper.ClassicalFourthData.Bq 8544
    have hp : val WuPaper.ClassicalFourthData.Bq 8544 = (276341417431285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8544 = 276341417431285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8544 = (517:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8545) ≤ val WuPaper.ClassicalFourthData.Bq 8545
    have hp : val WuPaper.ClassicalFourthData.Bq 8545 = (276343987598946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8545 = 276343987598946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8545 = (3309:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8546) ≤ val WuPaper.ClassicalFourthData.Bq 8546
    have hp : val WuPaper.ClassicalFourthData.Bq 8546 = (276346555919817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8546 = 276346555919817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8546 = (8273:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8547) ≤ val WuPaper.ClassicalFourthData.Bq 8547
    have hp : val WuPaper.ClassicalFourthData.Bq 8547 = (276349122394476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8547 = 276349122394476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8547 = (16547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8548) ≤ val WuPaper.ClassicalFourthData.Bq 8548
    have hp : val WuPaper.ClassicalFourthData.Bq 8548 = (276351687023503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8548 = 276351687023503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8548 = (4137:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8549) ≤ val WuPaper.ClassicalFourthData.Bq 8549
    have hp : val WuPaper.ClassicalFourthData.Bq 8549 = (276354249807477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8549 = 276354249807477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8549 = (16549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8550) ≤ val WuPaper.ClassicalFourthData.Bq 8550
    have hp : val WuPaper.ClassicalFourthData.Bq 8550 = (276356810746978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8550 = 276356810746978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8550 = (331:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8551) ≤ val WuPaper.ClassicalFourthData.Bq 8551
    have hp : val WuPaper.ClassicalFourthData.Bq 8551 = (276359369842584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8551 = 276359369842584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8551 = (16551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8551
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8552) ≤ val WuPaper.ClassicalFourthData.Bq 8552
    have hp : val WuPaper.ClassicalFourthData.Bq 8552 = (276361927094875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8552 = 276361927094875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8552 = (2069:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8553) ≤ val WuPaper.ClassicalFourthData.Bq 8553
    have hp : val WuPaper.ClassicalFourthData.Bq 8553 = (276364482504427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8553 = 276364482504427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8553 = (16553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8554) ≤ val WuPaper.ClassicalFourthData.Bq 8554
    have hp : val WuPaper.ClassicalFourthData.Bq 8554 = (276367036071820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8554 = 276367036071820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8554 = (8277:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8555) ≤ val WuPaper.ClassicalFourthData.Bq 8555
    have hp : val WuPaper.ClassicalFourthData.Bq 8555 = (276369587797633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8555 = 276369587797633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8555 = (3311:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8556) ≤ val WuPaper.ClassicalFourthData.Bq 8556
    have hp : val WuPaper.ClassicalFourthData.Bq 8556 = (276372137682442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8556 = 276372137682442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8556 = (4139:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8557) ≤ val WuPaper.ClassicalFourthData.Bq 8557
    have hp : val WuPaper.ClassicalFourthData.Bq 8557 = (276374685726825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8557 = 276374685726825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8557 = (16557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8558) ≤ val WuPaper.ClassicalFourthData.Bq 8558
    have hp : val WuPaper.ClassicalFourthData.Bq 8558 = (276377231931361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8558 = 276377231931361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8558 = (8279:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8559) ≤ val WuPaper.ClassicalFourthData.Bq 8559
    have hp : val WuPaper.ClassicalFourthData.Bq 8559 = (276379776296625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8559 = 276379776296625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8559 = (16559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_534
