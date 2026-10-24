import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints237
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_237 (j : Fin 16) (hj : 16*237+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*237+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*237+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3792) ≤ val WuPaper.ClassicalFourthData.Bq 3792
    have hp : val WuPaper.ClassicalFourthData.Bq 3792 = (226188332842722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3792 = 226188332842722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3792 = (737:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3793) ≤ val WuPaper.ClassicalFourthData.Bq 3793
    have hp : val WuPaper.ClassicalFourthData.Bq 3793 = (226212679976778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3793 = 226212679976778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3793 = (11793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3794) ≤ val WuPaper.ClassicalFourthData.Bq 3794
    have hp : val WuPaper.ClassicalFourthData.Bq 3794 = (226237017397534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3794 = 226237017397534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3794 = (5897:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3795) ≤ val WuPaper.ClassicalFourthData.Bq 3795
    have hp : val WuPaper.ClassicalFourthData.Bq 3795 = (226261345108894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3795 = 226261345108894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3795 = (2359:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3796) ≤ val WuPaper.ClassicalFourthData.Bq 3796
    have hp : val WuPaper.ClassicalFourthData.Bq 3796 = (226285663114759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3796 = 226285663114759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3796 = (2949:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3797) ≤ val WuPaper.ClassicalFourthData.Bq 3797
    have hp : val WuPaper.ClassicalFourthData.Bq 3797 = (226309971419030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3797 = 226309971419030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3797 = (11797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3798) ≤ val WuPaper.ClassicalFourthData.Bq 3798
    have hp : val WuPaper.ClassicalFourthData.Bq 3798 = (226334270025603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3798 = 226334270025603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3798 = (5899:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3799) ≤ val WuPaper.ClassicalFourthData.Bq 3799
    have hp : val WuPaper.ClassicalFourthData.Bq 3799 = (226358558938375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3799 = 226358558938375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3799 = (11799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3799
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3800) ≤ val WuPaper.ClassicalFourthData.Bq 3800
    have hp : val WuPaper.ClassicalFourthData.Bq 3800 = (226382838161240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3800 = 226382838161240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3800 = (59:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3801) ≤ val WuPaper.ClassicalFourthData.Bq 3801
    have hp : val WuPaper.ClassicalFourthData.Bq 3801 = (226407107698089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3801 = 226407107698089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3801 = (11801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3802) ≤ val WuPaper.ClassicalFourthData.Bq 3802
    have hp : val WuPaper.ClassicalFourthData.Bq 3802 = (226431367552813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3802 = 226431367552813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3802 = (5901:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3803) ≤ val WuPaper.ClassicalFourthData.Bq 3803
    have hp : val WuPaper.ClassicalFourthData.Bq 3803 = (226455617729301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3803 = 226455617729301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3803 = (11803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3804) ≤ val WuPaper.ClassicalFourthData.Bq 3804
    have hp : val WuPaper.ClassicalFourthData.Bq 3804 = (226479858231439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3804 = 226479858231439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3804 = (2951:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3805) ≤ val WuPaper.ClassicalFourthData.Bq 3805
    have hp : val WuPaper.ClassicalFourthData.Bq 3805 = (226504089063111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3805 = 226504089063111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3805 = (2361:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3806) ≤ val WuPaper.ClassicalFourthData.Bq 3806
    have hp : val WuPaper.ClassicalFourthData.Bq 3806 = (226528310228201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3806 = 226528310228201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3806 = (5903:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3807) ≤ val WuPaper.ClassicalFourthData.Bq 3807
    have hp : val WuPaper.ClassicalFourthData.Bq 3807 = (226552521730589:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3807 = 226552521730589 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3807 = (11807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_237
