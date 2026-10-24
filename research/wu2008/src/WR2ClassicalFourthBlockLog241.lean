import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints241
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_241 (j : Fin 16) (hj : 16*241+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*241+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*241+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3856) ≤ val WuPaper.ClassicalFourthData.Bq 3856
    have hp : val WuPaper.ClassicalFourthData.Bq 3856 = (227727128857043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3856 = 227727128857043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3856 = (741:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3857) ≤ val WuPaper.ClassicalFourthData.Bq 3857
    have hp : val WuPaper.ClassicalFourthData.Bq 3857 = (227750862131668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3857 = 227750862131668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3857 = (11857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3858) ≤ val WuPaper.ClassicalFourthData.Bq 3858
    have hp : val WuPaper.ClassicalFourthData.Bq 3858 = (227774585939072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3858 = 227774585939072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3858 = (5929:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3859) ≤ val WuPaper.ClassicalFourthData.Bq 3859
    have hp : val WuPaper.ClassicalFourthData.Bq 3859 = (227798300283042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3859 = 227798300283042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3859 = (11859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3860) ≤ val WuPaper.ClassicalFourthData.Bq 3860
    have hp : val WuPaper.ClassicalFourthData.Bq 3860 = (227822005167361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3860 = 227822005167361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3860 = (593:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3861) ≤ val WuPaper.ClassicalFourthData.Bq 3861
    have hp : val WuPaper.ClassicalFourthData.Bq 3861 = (227845700595812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3861 = 227845700595812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3861 = (11861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3862) ≤ val WuPaper.ClassicalFourthData.Bq 3862
    have hp : val WuPaper.ClassicalFourthData.Bq 3862 = (227869386572173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3862 = 227869386572173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3862 = (5931:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3863) ≤ val WuPaper.ClassicalFourthData.Bq 3863
    have hp : val WuPaper.ClassicalFourthData.Bq 3863 = (227893063100224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3863 = 227893063100224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3863 = (11863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3863
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3864) ≤ val WuPaper.ClassicalFourthData.Bq 3864
    have hp : val WuPaper.ClassicalFourthData.Bq 3864 = (227916730183741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3864 = 227916730183741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3864 = (1483:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3865) ≤ val WuPaper.ClassicalFourthData.Bq 3865
    have hp : val WuPaper.ClassicalFourthData.Bq 3865 = (227940387826499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3865 = 227940387826499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3865 = (2373:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3866) ≤ val WuPaper.ClassicalFourthData.Bq 3866
    have hp : val WuPaper.ClassicalFourthData.Bq 3866 = (227964036032270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3866 = 227964036032270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3866 = (5933:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3867) ≤ val WuPaper.ClassicalFourthData.Bq 3867
    have hp : val WuPaper.ClassicalFourthData.Bq 3867 = (227987674804826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3867 = 227987674804826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3867 = (11867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3868) ≤ val WuPaper.ClassicalFourthData.Bq 3868
    have hp : val WuPaper.ClassicalFourthData.Bq 3868 = (228011304147935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3868 = 228011304147935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3868 = (2967:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3869) ≤ val WuPaper.ClassicalFourthData.Bq 3869
    have hp : val WuPaper.ClassicalFourthData.Bq 3869 = (228034924065366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3869 = 228034924065366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3869 = (11869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3870) ≤ val WuPaper.ClassicalFourthData.Bq 3870
    have hp : val WuPaper.ClassicalFourthData.Bq 3870 = (228058534560884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3870 = 228058534560884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3870 = (1187:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3871) ≤ val WuPaper.ClassicalFourthData.Bq 3871
    have hp : val WuPaper.ClassicalFourthData.Bq 3871 = (228082135638253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3871 = 228082135638253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3871 = (11871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_241
