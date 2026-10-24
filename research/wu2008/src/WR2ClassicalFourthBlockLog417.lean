import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints417
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_417 (j : Fin 16) (hj : 16*417+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*417+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*417+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6672) ≤ val WuPaper.ClassicalFourthData.Bq 6672
    have hp : val WuPaper.ClassicalFourthData.Bq 6672 = (267537930221780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6672 = 267537930221780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6672 = (917:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6673) ≤ val WuPaper.ClassicalFourthData.Bq 6673
    have hp : val WuPaper.ClassicalFourthData.Bq 6673 = (267545240049628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6673 = 267545240049628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6673 = (14673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6674) ≤ val WuPaper.ClassicalFourthData.Bq 6674
    have hp : val WuPaper.ClassicalFourthData.Bq 6674 = (267552546488204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6674 = 267552546488204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6674 = (7337:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6675) ≤ val WuPaper.ClassicalFourthData.Bq 6675
    have hp : val WuPaper.ClassicalFourthData.Bq 6675 = (267559849538647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6675 = 267559849538647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6675 = (587:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6676) ≤ val WuPaper.ClassicalFourthData.Bq 6676
    have hp : val WuPaper.ClassicalFourthData.Bq 6676 = (267567149202099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6676 = 267567149202099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6676 = (3669:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6677) ≤ val WuPaper.ClassicalFourthData.Bq 6677
    have hp : val WuPaper.ClassicalFourthData.Bq 6677 = (267574445479700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6677 = 267574445479700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6677 = (14677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6678) ≤ val WuPaper.ClassicalFourthData.Bq 6678
    have hp : val WuPaper.ClassicalFourthData.Bq 6678 = (267581738372590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6678 = 267581738372590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6678 = (7339:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6679) ≤ val WuPaper.ClassicalFourthData.Bq 6679
    have hp : val WuPaper.ClassicalFourthData.Bq 6679 = (267589027881908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6679 = 267589027881908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6679 = (14679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6679
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6680) ≤ val WuPaper.ClassicalFourthData.Bq 6680
    have hp : val WuPaper.ClassicalFourthData.Bq 6680 = (267596314008794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6680 = 267596314008794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6680 = (367:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6681) ≤ val WuPaper.ClassicalFourthData.Bq 6681
    have hp : val WuPaper.ClassicalFourthData.Bq 6681 = (267603596754385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6681 = 267603596754385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6681 = (14681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6682) ≤ val WuPaper.ClassicalFourthData.Bq 6682
    have hp : val WuPaper.ClassicalFourthData.Bq 6682 = (267610876119821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6682 = 267610876119821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6682 = (7341:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6683) ≤ val WuPaper.ClassicalFourthData.Bq 6683
    have hp : val WuPaper.ClassicalFourthData.Bq 6683 = (267618152106239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6683 = 267618152106239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6683 = (14683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6684) ≤ val WuPaper.ClassicalFourthData.Bq 6684
    have hp : val WuPaper.ClassicalFourthData.Bq 6684 = (267625424714775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6684 = 267625424714775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6684 = (3671:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6685) ≤ val WuPaper.ClassicalFourthData.Bq 6685
    have hp : val WuPaper.ClassicalFourthData.Bq 6685 = (267632693946568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6685 = 267632693946568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6685 = (2937:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6686) ≤ val WuPaper.ClassicalFourthData.Bq 6686
    have hp : val WuPaper.ClassicalFourthData.Bq 6686 = (267639959802752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6686 = 267639959802752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6686 = (7343:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6687) ≤ val WuPaper.ClassicalFourthData.Bq 6687
    have hp : val WuPaper.ClassicalFourthData.Bq 6687 = (267647222284465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6687 = 267647222284465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6687 = (14687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_417
