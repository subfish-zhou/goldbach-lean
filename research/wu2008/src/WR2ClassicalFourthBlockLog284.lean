import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints284
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_284 (j : Fin 16) (hj : 16*284+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*284+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*284+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4544) ≤ val WuPaper.ClassicalFourthData.Bq 4544
    have hp : val WuPaper.ClassicalFourthData.Bq 4544 = (242007309023581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4544 = 242007309023581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4544 = (392:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4545) ≤ val WuPaper.ClassicalFourthData.Bq 4545
    have hp : val WuPaper.ClassicalFourthData.Bq 4545 = (242025334538913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4545 = 242025334538913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4545 = (2509:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4546) ≤ val WuPaper.ClassicalFourthData.Bq 4546
    have hp : val WuPaper.ClassicalFourthData.Bq 4546 = (242043352814266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4546 = 242043352814266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4546 = (6273:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4547) ≤ val WuPaper.ClassicalFourthData.Bq 4547
    have hp : val WuPaper.ClassicalFourthData.Bq 4547 = (242061363852392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4547 = 242061363852392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4547 = (12547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4548) ≤ val WuPaper.ClassicalFourthData.Bq 4548
    have hp : val WuPaper.ClassicalFourthData.Bq 4548 = (242079367656045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4548 = 242079367656045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4548 = (3137:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4549) ≤ val WuPaper.ClassicalFourthData.Bq 4549
    have hp : val WuPaper.ClassicalFourthData.Bq 4549 = (242097364227973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4549 = 242097364227973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4549 = (12549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4550) ≤ val WuPaper.ClassicalFourthData.Bq 4550
    have hp : val WuPaper.ClassicalFourthData.Bq 4550 = (242115353570926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4550 = 242115353570926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4550 = (251:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4551) ≤ val WuPaper.ClassicalFourthData.Bq 4551
    have hp : val WuPaper.ClassicalFourthData.Bq 4551 = (242133335687652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4551 = 242133335687652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4551 = (12551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4551
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4552) ≤ val WuPaper.ClassicalFourthData.Bq 4552
    have hp : val WuPaper.ClassicalFourthData.Bq 4552 = (242151310580897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4552 = 242151310580897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4552 = (1569:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4553) ≤ val WuPaper.ClassicalFourthData.Bq 4553
    have hp : val WuPaper.ClassicalFourthData.Bq 4553 = (242169278253407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4553 = 242169278253407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4553 = (12553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4554) ≤ val WuPaper.ClassicalFourthData.Bq 4554
    have hp : val WuPaper.ClassicalFourthData.Bq 4554 = (242187238707927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4554 = 242187238707927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4554 = (6277:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4555) ≤ val WuPaper.ClassicalFourthData.Bq 4555
    have hp : val WuPaper.ClassicalFourthData.Bq 4555 = (242205191947198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4555 = 242205191947198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4555 = (2511:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4556) ≤ val WuPaper.ClassicalFourthData.Bq 4556
    have hp : val WuPaper.ClassicalFourthData.Bq 4556 = (242223137973963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4556 = 242223137973963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4556 = (3139:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4557) ≤ val WuPaper.ClassicalFourthData.Bq 4557
    have hp : val WuPaper.ClassicalFourthData.Bq 4557 = (242241076790962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4557 = 242241076790962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4557 = (12557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4558) ≤ val WuPaper.ClassicalFourthData.Bq 4558
    have hp : val WuPaper.ClassicalFourthData.Bq 4558 = (242259008400935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4558 = 242259008400935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4558 = (6279:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4559) ≤ val WuPaper.ClassicalFourthData.Bq 4559
    have hp : val WuPaper.ClassicalFourthData.Bq 4559 = (242276932806620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4559 = 242276932806620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4559 = (12559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_284
