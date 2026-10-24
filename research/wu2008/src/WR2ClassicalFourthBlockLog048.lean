import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints048
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_048 (j : Fin 16) (hj : 16*48+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*48+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*48+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 768) ≤ val WuPaper.ClassicalFourthData.Bq 768
    have hp : val WuPaper.ClassicalFourthData.Bq 768 = (80124347008740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 768 = 80124347008740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 768 = (274:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 769) ≤ val WuPaper.ClassicalFourthData.Bq 769
    have hp : val WuPaper.ClassicalFourthData.Bq 769 = (80210869287808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 769 = 80210869287808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 769 = (8769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 770) ≤ val WuPaper.ClassicalFourthData.Bq 770
    have hp : val WuPaper.ClassicalFourthData.Bq 770 = (80297351781236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 770 = 80297351781236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 770 = (877:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 771) ≤ val WuPaper.ClassicalFourthData.Bq 771
    have hp : val WuPaper.ClassicalFourthData.Bq 771 = (80383794511039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 771 = 80383794511039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 771 = (8771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 772) ≤ val WuPaper.ClassicalFourthData.Bq 772
    have hp : val WuPaper.ClassicalFourthData.Bq 772 = (80470197499216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 772 = 80470197499216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 772 = (2193:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 773) ≤ val WuPaper.ClassicalFourthData.Bq 773
    have hp : val WuPaper.ClassicalFourthData.Bq 773 = (80556560767751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 773 = 80556560767751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 773 = (8773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 774) ≤ val WuPaper.ClassicalFourthData.Bq 774
    have hp : val WuPaper.ClassicalFourthData.Bq 774 = (80642884338614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 774 = 80642884338614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 774 = (4387:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 775) ≤ val WuPaper.ClassicalFourthData.Bq 775
    have hp : val WuPaper.ClassicalFourthData.Bq 775 = (80729168233757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 775 = 80729168233757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 775 = (351:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_775
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 776) ≤ val WuPaper.ClassicalFourthData.Bq 776
    have hp : val WuPaper.ClassicalFourthData.Bq 776 = (80815412475119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 776 = 80815412475119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 776 = (1097:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 777) ≤ val WuPaper.ClassicalFourthData.Bq 777
    have hp : val WuPaper.ClassicalFourthData.Bq 777 = (80901617084624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 777 = 80901617084624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 777 = (8777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 778) ≤ val WuPaper.ClassicalFourthData.Bq 778
    have hp : val WuPaper.ClassicalFourthData.Bq 778 = (80987782084178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 778 = 80987782084178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 778 = (4389:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 779) ≤ val WuPaper.ClassicalFourthData.Bq 779
    have hp : val WuPaper.ClassicalFourthData.Bq 779 = (81073907495675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 779 = 81073907495675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 779 = (8779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 780) ≤ val WuPaper.ClassicalFourthData.Bq 780
    have hp : val WuPaper.ClassicalFourthData.Bq 780 = (81159993340991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 780 = 81159993340991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 780 = (439:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 781) ≤ val WuPaper.ClassicalFourthData.Bq 781
    have hp : val WuPaper.ClassicalFourthData.Bq 781 = (81246039641989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 781 = 81246039641989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 781 = (8781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 782) ≤ val WuPaper.ClassicalFourthData.Bq 782
    have hp : val WuPaper.ClassicalFourthData.Bq 782 = (81332046420516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 782 = 81332046420516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 782 = (4391:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 783) ≤ val WuPaper.ClassicalFourthData.Bq 783
    have hp : val WuPaper.ClassicalFourthData.Bq 783 = (81418013698404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 783 = 81418013698404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 783 = (8783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_048
