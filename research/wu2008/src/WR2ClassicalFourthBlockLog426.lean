import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints426
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_426 (j : Fin 16) (hj : 16*426+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*426+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*426+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6816) ≤ val WuPaper.ClassicalFourthData.Bq 6816
    have hp : val WuPaper.ClassicalFourthData.Bq 6816 = (268556198212981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6816 = 268556198212981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6816 = (463:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6817) ≤ val WuPaper.ClassicalFourthData.Bq 6817
    have hp : val WuPaper.ClassicalFourthData.Bq 6817 = (268563031525525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6817 = 268563031525525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6817 = (14817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6818) ≤ val WuPaper.ClassicalFourthData.Bq 6818
    have hp : val WuPaper.ClassicalFourthData.Bq 6818 = (268569861608721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6818 = 268569861608721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6818 = (7409:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6819) ≤ val WuPaper.ClassicalFourthData.Bq 6819
    have hp : val WuPaper.ClassicalFourthData.Bq 6819 = (268576688463651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6819 = 268576688463651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6819 = (14819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6820) ≤ val WuPaper.ClassicalFourthData.Bq 6820
    have hp : val WuPaper.ClassicalFourthData.Bq 6820 = (268583512091392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6820 = 268583512091392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6820 = (741:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6821) ≤ val WuPaper.ClassicalFourthData.Bq 6821
    have hp : val WuPaper.ClassicalFourthData.Bq 6821 = (268590332493026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6821 = 268590332493026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6821 = (14821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6822) ≤ val WuPaper.ClassicalFourthData.Bq 6822
    have hp : val WuPaper.ClassicalFourthData.Bq 6822 = (268597149669631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6822 = 268597149669631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6822 = (7411:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6823) ≤ val WuPaper.ClassicalFourthData.Bq 6823
    have hp : val WuPaper.ClassicalFourthData.Bq 6823 = (268603963622285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6823 = 268603963622285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6823 = (14823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6823
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6824) ≤ val WuPaper.ClassicalFourthData.Bq 6824
    have hp : val WuPaper.ClassicalFourthData.Bq 6824 = (268610774352068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6824 = 268610774352068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6824 = (1853:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6825) ≤ val WuPaper.ClassicalFourthData.Bq 6825
    have hp : val WuPaper.ClassicalFourthData.Bq 6825 = (268617581860055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6825 = 268617581860055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6825 = (593:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6826) ≤ val WuPaper.ClassicalFourthData.Bq 6826
    have hp : val WuPaper.ClassicalFourthData.Bq 6826 = (268624386147326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6826 = 268624386147326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6826 = (7413:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6827) ≤ val WuPaper.ClassicalFourthData.Bq 6827
    have hp : val WuPaper.ClassicalFourthData.Bq 6827 = (268631187214956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6827 = 268631187214956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6827 = (14827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6828) ≤ val WuPaper.ClassicalFourthData.Bq 6828
    have hp : val WuPaper.ClassicalFourthData.Bq 6828 = (268637985064023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6828 = 268637985064023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6828 = (3707:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6829) ≤ val WuPaper.ClassicalFourthData.Bq 6829
    have hp : val WuPaper.ClassicalFourthData.Bq 6829 = (268644779695602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6829 = 268644779695602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6829 = (14829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6830) ≤ val WuPaper.ClassicalFourthData.Bq 6830
    have hp : val WuPaper.ClassicalFourthData.Bq 6830 = (268651571110769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6830 = 268651571110769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6830 = (1483:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6831) ≤ val WuPaper.ClassicalFourthData.Bq 6831
    have hp : val WuPaper.ClassicalFourthData.Bq 6831 = (268658359310600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6831 = 268658359310600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6831 = (14831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_426
