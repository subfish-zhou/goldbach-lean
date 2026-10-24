import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints354
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_354 (j : Fin 16) (hj : 16*354+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*354+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*354+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5664) ≤ val WuPaper.ClassicalFourthData.Bq 5664
    have hp : val WuPaper.ClassicalFourthData.Bq 5664 = (258229882925227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5664 = 258229882925227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5664 = (427:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5665) ≤ val WuPaper.ClassicalFourthData.Bq 5665
    have hp : val WuPaper.ClassicalFourthData.Bq 5665 = (258241273776922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5665 = 258241273776922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5665 = (2733:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5666) ≤ val WuPaper.ClassicalFourthData.Bq 5666
    have hp : val WuPaper.ClassicalFourthData.Bq 5666 = (258252659828189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5666 = 258252659828189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5666 = (6833:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5667) ≤ val WuPaper.ClassicalFourthData.Bq 5667
    have hp : val WuPaper.ClassicalFourthData.Bq 5667 = (258264041080730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5667 = 258264041080730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5667 = (13667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5668) ≤ val WuPaper.ClassicalFourthData.Bq 5668
    have hp : val WuPaper.ClassicalFourthData.Bq 5668 = (258275417536246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5668 = 258275417536246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5668 = (3417:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5669) ≤ val WuPaper.ClassicalFourthData.Bq 5669
    have hp : val WuPaper.ClassicalFourthData.Bq 5669 = (258286789196438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5669 = 258286789196438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5669 = (13669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5670) ≤ val WuPaper.ClassicalFourthData.Bq 5670
    have hp : val WuPaper.ClassicalFourthData.Bq 5670 = (258298156063005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5670 = 258298156063005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5670 = (1367:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5671) ≤ val WuPaper.ClassicalFourthData.Bq 5671
    have hp : val WuPaper.ClassicalFourthData.Bq 5671 = (258309518137647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5671 = 258309518137647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5671 = (13671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5671
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5672) ≤ val WuPaper.ClassicalFourthData.Bq 5672
    have hp : val WuPaper.ClassicalFourthData.Bq 5672 = (258320875422062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5672 = 258320875422062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5672 = (1709:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5673) ≤ val WuPaper.ClassicalFourthData.Bq 5673
    have hp : val WuPaper.ClassicalFourthData.Bq 5673 = (258332227917948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5673 = 258332227917948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5673 = (13673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5674) ≤ val WuPaper.ClassicalFourthData.Bq 5674
    have hp : val WuPaper.ClassicalFourthData.Bq 5674 = (258343575627003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5674 = 258343575627003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5674 = (6837:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5675) ≤ val WuPaper.ClassicalFourthData.Bq 5675
    have hp : val WuPaper.ClassicalFourthData.Bq 5675 = (258354918550921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5675 = 258354918550921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5675 = (547:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5676) ≤ val WuPaper.ClassicalFourthData.Bq 5676
    have hp : val WuPaper.ClassicalFourthData.Bq 5676 = (258366256691400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5676 = 258366256691400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5676 = (3419:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5677) ≤ val WuPaper.ClassicalFourthData.Bq 5677
    have hp : val WuPaper.ClassicalFourthData.Bq 5677 = (258377590050135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5677 = 258377590050135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5677 = (13677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5678) ≤ val WuPaper.ClassicalFourthData.Bq 5678
    have hp : val WuPaper.ClassicalFourthData.Bq 5678 = (258388918628818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5678 = 258388918628818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5678 = (6839:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5679) ≤ val WuPaper.ClassicalFourthData.Bq 5679
    have hp : val WuPaper.ClassicalFourthData.Bq 5679 = (258400242429145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5679 = 258400242429145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5679 = (13679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5679
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_354
