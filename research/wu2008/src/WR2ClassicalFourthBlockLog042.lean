import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints042
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_042 (j : Fin 16) (hj : 16*42+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*42+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*42+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 672) ≤ val WuPaper.ClassicalFourthData.Bq 672
    have hp : val WuPaper.ClassicalFourthData.Bq 672 = (71629559227877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 672 = 71629559227877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 672 = (271:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 673) ≤ val WuPaper.ClassicalFourthData.Bq 673
    have hp : val WuPaper.ClassicalFourthData.Bq 673 = (71720005810400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 673 = 71720005810400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 673 = (8673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 674) ≤ val WuPaper.ClassicalFourthData.Bq 674
    have hp : val WuPaper.ClassicalFourthData.Bq 674 = (71810410420464:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 674 = 71810410420464 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 674 = (4337:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 675) ≤ val WuPaper.ClassicalFourthData.Bq 675
    have hp : val WuPaper.ClassicalFourthData.Bq 675 = (71900773081619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 675 = 71900773081619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 675 = (347:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 676) ≤ val WuPaper.ClassicalFourthData.Bq 676
    have hp : val WuPaper.ClassicalFourthData.Bq 676 = (71991093817396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 676 = 71991093817396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 676 = (2169:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 677) ≤ val WuPaper.ClassicalFourthData.Bq 677
    have hp : val WuPaper.ClassicalFourthData.Bq 677 = (72081372651312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 677 = 72081372651312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 677 = (8677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 678) ≤ val WuPaper.ClassicalFourthData.Bq 678
    have hp : val WuPaper.ClassicalFourthData.Bq 678 = (72171609606867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 678 = 72171609606867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 678 = (4339:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 679) ≤ val WuPaper.ClassicalFourthData.Bq 679
    have hp : val WuPaper.ClassicalFourthData.Bq 679 = (72261804707542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 679 = 72261804707542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 679 = (8679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_679
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 680) ≤ val WuPaper.ClassicalFourthData.Bq 680
    have hp : val WuPaper.ClassicalFourthData.Bq 680 = (72351957976805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 680 = 72351957976805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 680 = (217:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 681) ≤ val WuPaper.ClassicalFourthData.Bq 681
    have hp : val WuPaper.ClassicalFourthData.Bq 681 = (72442069438103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 681 = 72442069438103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 681 = (8681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 682) ≤ val WuPaper.ClassicalFourthData.Bq 682
    have hp : val WuPaper.ClassicalFourthData.Bq 682 = (72532139114872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 682 = 72532139114872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 682 = (4341:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 683) ≤ val WuPaper.ClassicalFourthData.Bq 683
    have hp : val WuPaper.ClassicalFourthData.Bq 683 = (72622167030526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 683 = 72622167030526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 683 = (8683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 684) ≤ val WuPaper.ClassicalFourthData.Bq 684
    have hp : val WuPaper.ClassicalFourthData.Bq 684 = (72712153208467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 684 = 72712153208467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 684 = (2171:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 685) ≤ val WuPaper.ClassicalFourthData.Bq 685
    have hp : val WuPaper.ClassicalFourthData.Bq 685 = (72802097672076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 685 = 72802097672076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 685 = (1737:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 686) ≤ val WuPaper.ClassicalFourthData.Bq 686
    have hp : val WuPaper.ClassicalFourthData.Bq 686 = (72892000444722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 686 = 72892000444722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 686 = (4343:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 687) ≤ val WuPaper.ClassicalFourthData.Bq 687
    have hp : val WuPaper.ClassicalFourthData.Bq 687 = (72981861549755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 687 = 72981861549755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 687 = (8687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_042
