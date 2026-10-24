import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints172
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_172 (j : Fin 16) (hj : 16*172+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*172+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*172+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2752) ≤ val WuPaper.ClassicalFourthData.Bq 2752
    have hp : val WuPaper.ClassicalFourthData.Bq 2752 = (194770980719407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2752 = 194770980719407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2752 = (336:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2753) ≤ val WuPaper.ClassicalFourthData.Bq 2753
    have hp : val WuPaper.ClassicalFourthData.Bq 2753 = (194807956653144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2753 = 194807956653144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2753 = (10753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2754) ≤ val WuPaper.ClassicalFourthData.Bq 2754
    have hp : val WuPaper.ClassicalFourthData.Bq 2754 = (194844917553835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2754 = 194844917553835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2754 = (5377:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2755) ≤ val WuPaper.ClassicalFourthData.Bq 2755
    have hp : val WuPaper.ClassicalFourthData.Bq 2755 = (194881863428088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2755 = 194881863428088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2755 = (2151:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2756) ≤ val WuPaper.ClassicalFourthData.Bq 2756
    have hp : val WuPaper.ClassicalFourthData.Bq 2756 = (194918794282508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2756 = 194918794282508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2756 = (2689:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2757) ≤ val WuPaper.ClassicalFourthData.Bq 2757
    have hp : val WuPaper.ClassicalFourthData.Bq 2757 = (194955710123696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2757 = 194955710123696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2757 = (10757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2758) ≤ val WuPaper.ClassicalFourthData.Bq 2758
    have hp : val WuPaper.ClassicalFourthData.Bq 2758 = (194992610958248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2758 = 194992610958248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2758 = (5379:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2759) ≤ val WuPaper.ClassicalFourthData.Bq 2759
    have hp : val WuPaper.ClassicalFourthData.Bq 2759 = (195029496792761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2759 = 195029496792761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2759 = (10759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2759
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2760) ≤ val WuPaper.ClassicalFourthData.Bq 2760
    have hp : val WuPaper.ClassicalFourthData.Bq 2760 = (195066367633823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2760 = 195066367633823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2760 = (269:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2761) ≤ val WuPaper.ClassicalFourthData.Bq 2761
    have hp : val WuPaper.ClassicalFourthData.Bq 2761 = (195103223488022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2761 = 195103223488022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2761 = (10761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2762) ≤ val WuPaper.ClassicalFourthData.Bq 2762
    have hp : val WuPaper.ClassicalFourthData.Bq 2762 = (195140064361942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2762 = 195140064361942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2762 = (5381:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2763) ≤ val WuPaper.ClassicalFourthData.Bq 2763
    have hp : val WuPaper.ClassicalFourthData.Bq 2763 = (195176890262162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2763 = 195176890262162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2763 = (10763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2764) ≤ val WuPaper.ClassicalFourthData.Bq 2764
    have hp : val WuPaper.ClassicalFourthData.Bq 2764 = (195213701195260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2764 = 195213701195260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2764 = (2691:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2765) ≤ val WuPaper.ClassicalFourthData.Bq 2765
    have hp : val WuPaper.ClassicalFourthData.Bq 2765 = (195250497167808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2765 = 195250497167808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2765 = (2153:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2766) ≤ val WuPaper.ClassicalFourthData.Bq 2766
    have hp : val WuPaper.ClassicalFourthData.Bq 2766 = (195287278186375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2766 = 195287278186375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2766 = (5383:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2767) ≤ val WuPaper.ClassicalFourthData.Bq 2767
    have hp : val WuPaper.ClassicalFourthData.Bq 2767 = (195324044257527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2767 = 195324044257527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2767 = (10767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2767
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_172
