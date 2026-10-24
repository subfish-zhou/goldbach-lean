import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints239
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_239 (j : Fin 16) (hj : 16*239+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*239+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*239+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3824) ≤ val WuPaper.ClassicalFourthData.Bq 3824
    have hp : val WuPaper.ClassicalFourthData.Bq 3824 = (226962642629441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3824 = 226962642629441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3824 = (739:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3825) ≤ val WuPaper.ClassicalFourthData.Bq 3825
    have hp : val WuPaper.ClassicalFourthData.Bq 3825 = (226986680864720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3825 = 226986680864720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3825 = (473:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3826) ≤ val WuPaper.ClassicalFourthData.Bq 3826
    have hp : val WuPaper.ClassicalFourthData.Bq 3826 = (227010709510682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3826 = 227010709510682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3826 = (5913:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3827) ≤ val WuPaper.ClassicalFourthData.Bq 3827
    have hp : val WuPaper.ClassicalFourthData.Bq 3827 = (227034728571172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3827 = 227034728571172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3827 = (11827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3828) ≤ val WuPaper.ClassicalFourthData.Bq 3828
    have hp : val WuPaper.ClassicalFourthData.Bq 3828 = (227058738050031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3828 = 227058738050031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3828 = (2957:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3829) ≤ val WuPaper.ClassicalFourthData.Bq 3829
    have hp : val WuPaper.ClassicalFourthData.Bq 3829 = (227082737951099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3829 = 227082737951099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3829 = (11829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3830) ≤ val WuPaper.ClassicalFourthData.Bq 3830
    have hp : val WuPaper.ClassicalFourthData.Bq 3830 = (227106728278216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3830 = 227106728278216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3830 = (1183:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3831) ≤ val WuPaper.ClassicalFourthData.Bq 3831
    have hp : val WuPaper.ClassicalFourthData.Bq 3831 = (227130709035216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3831 = 227130709035216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3831 = (11831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3831
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3832) ≤ val WuPaper.ClassicalFourthData.Bq 3832
    have hp : val WuPaper.ClassicalFourthData.Bq 3832 = (227154680225936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3832 = 227154680225936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3832 = (1479:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3833) ≤ val WuPaper.ClassicalFourthData.Bq 3833
    have hp : val WuPaper.ClassicalFourthData.Bq 3833 = (227178641854209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3833 = 227178641854209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3833 = (11833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3834) ≤ val WuPaper.ClassicalFourthData.Bq 3834
    have hp : val WuPaper.ClassicalFourthData.Bq 3834 = (227202593923864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3834 = 227202593923864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3834 = (5917:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3835) ≤ val WuPaper.ClassicalFourthData.Bq 3835
    have hp : val WuPaper.ClassicalFourthData.Bq 3835 = (227226536438731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3835 = 227226536438731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3835 = (2367:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3836) ≤ val WuPaper.ClassicalFourthData.Bq 3836
    have hp : val WuPaper.ClassicalFourthData.Bq 3836 = (227250469402638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3836 = 227250469402638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3836 = (2959:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3837) ≤ val WuPaper.ClassicalFourthData.Bq 3837
    have hp : val WuPaper.ClassicalFourthData.Bq 3837 = (227274392819410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3837 = 227274392819410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3837 = (11837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3838) ≤ val WuPaper.ClassicalFourthData.Bq 3838
    have hp : val WuPaper.ClassicalFourthData.Bq 3838 = (227298306692871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3838 = 227298306692871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3838 = (5919:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3839) ≤ val WuPaper.ClassicalFourthData.Bq 3839
    have hp : val WuPaper.ClassicalFourthData.Bq 3839 = (227322211026842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3839 = 227322211026842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3839 = (11839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_239
