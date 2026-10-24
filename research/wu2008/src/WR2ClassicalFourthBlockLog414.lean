import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints414
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_414 (j : Fin 16) (hj : 16*414+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*414+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*414+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6624) ≤ val WuPaper.ClassicalFourthData.Bq 6624
    have hp : val WuPaper.ClassicalFourthData.Bq 6624 = (267183050222726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6624 = 267183050222726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6624 = (457:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6625) ≤ val WuPaper.ClassicalFourthData.Bq 6625
    have hp : val WuPaper.ClassicalFourthData.Bq 6625 = (267190524086342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6625 = 267190524086342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6625 = (117:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6626) ≤ val WuPaper.ClassicalFourthData.Bq 6626
    have hp : val WuPaper.ClassicalFourthData.Bq 6626 = (267197994505390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6626 = 267197994505390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6626 = (7313:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6627) ≤ val WuPaper.ClassicalFourthData.Bq 6627
    have hp : val WuPaper.ClassicalFourthData.Bq 6627 = (267205461481033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6627 = 267205461481033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6627 = (14627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6628) ≤ val WuPaper.ClassicalFourthData.Bq 6628
    have hp : val WuPaper.ClassicalFourthData.Bq 6628 = (267212925014432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6628 = 267212925014432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6628 = (3657:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6629) ≤ val WuPaper.ClassicalFourthData.Bq 6629
    have hp : val WuPaper.ClassicalFourthData.Bq 6629 = (267220385106748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6629 = 267220385106748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6629 = (14629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6630) ≤ val WuPaper.ClassicalFourthData.Bq 6630
    have hp : val WuPaper.ClassicalFourthData.Bq 6630 = (267227841759143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6630 = 267227841759143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6630 = (1463:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6631) ≤ val WuPaper.ClassicalFourthData.Bq 6631
    have hp : val WuPaper.ClassicalFourthData.Bq 6631 = (267235294972778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6631 = 267235294972778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6631 = (14631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6631
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6632) ≤ val WuPaper.ClassicalFourthData.Bq 6632
    have hp : val WuPaper.ClassicalFourthData.Bq 6632 = (267242744748812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6632 = 267242744748812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6632 = (1829:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6633) ≤ val WuPaper.ClassicalFourthData.Bq 6633
    have hp : val WuPaper.ClassicalFourthData.Bq 6633 = (267250191088406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6633 = 267250191088406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6633 = (14633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6634) ≤ val WuPaper.ClassicalFourthData.Bq 6634
    have hp : val WuPaper.ClassicalFourthData.Bq 6634 = (267257633992718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6634 = 267257633992718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6634 = (7317:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6635) ≤ val WuPaper.ClassicalFourthData.Bq 6635
    have hp : val WuPaper.ClassicalFourthData.Bq 6635 = (267265073462907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6635 = 267265073462907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6635 = (2927:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6636) ≤ val WuPaper.ClassicalFourthData.Bq 6636
    have hp : val WuPaper.ClassicalFourthData.Bq 6636 = (267272509500132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6636 = 267272509500132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6636 = (3659:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6637) ≤ val WuPaper.ClassicalFourthData.Bq 6637
    have hp : val WuPaper.ClassicalFourthData.Bq 6637 = (267279942105551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6637 = 267279942105551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6637 = (14637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6638) ≤ val WuPaper.ClassicalFourthData.Bq 6638
    have hp : val WuPaper.ClassicalFourthData.Bq 6638 = (267287371280322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6638 = 267287371280322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6638 = (7319:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6639) ≤ val WuPaper.ClassicalFourthData.Bq 6639
    have hp : val WuPaper.ClassicalFourthData.Bq 6639 = (267294797025600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6639 = 267294797025600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6639 = (14639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_414
