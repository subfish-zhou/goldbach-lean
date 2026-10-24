import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints432
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_432 (j : Fin 16) (hj : 16*432+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*432+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*432+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6912) ≤ val WuPaper.ClassicalFourthData.Bq 6912
    have hp : val WuPaper.ClassicalFourthData.Bq 6912 = (269197623385575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6912 = 269197623385575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6912 = (466:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6913) ≤ val WuPaper.ClassicalFourthData.Bq 6913
    have hp : val WuPaper.ClassicalFourthData.Bq 6913 = (269204151548654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6913 = 269204151548654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6913 = (14913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6914) ≤ val WuPaper.ClassicalFourthData.Bq 6914
    have hp : val WuPaper.ClassicalFourthData.Bq 6914 = (269210676584245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6914 = 269210676584245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6914 = (7457:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6915) ≤ val WuPaper.ClassicalFourthData.Bq 6915
    have hp : val WuPaper.ClassicalFourthData.Bq 6915 = (269217198493389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6915 = 269217198493389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6915 = (2983:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6916) ≤ val WuPaper.ClassicalFourthData.Bq 6916
    have hp : val WuPaper.ClassicalFourthData.Bq 6916 = (269223717277128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6916 = 269223717277128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6916 = (3729:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6917) ≤ val WuPaper.ClassicalFourthData.Bq 6917
    have hp : val WuPaper.ClassicalFourthData.Bq 6917 = (269230232936503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6917 = 269230232936503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6917 = (14917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6918) ≤ val WuPaper.ClassicalFourthData.Bq 6918
    have hp : val WuPaper.ClassicalFourthData.Bq 6918 = (269236745472553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6918 = 269236745472553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6918 = (7459:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6919) ≤ val WuPaper.ClassicalFourthData.Bq 6919
    have hp : val WuPaper.ClassicalFourthData.Bq 6919 = (269243254886319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6919 = 269243254886319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6919 = (14919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6919
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6920) ≤ val WuPaper.ClassicalFourthData.Bq 6920
    have hp : val WuPaper.ClassicalFourthData.Bq 6920 = (269249761178842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6920 = 269249761178842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6920 = (373:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6921) ≤ val WuPaper.ClassicalFourthData.Bq 6921
    have hp : val WuPaper.ClassicalFourthData.Bq 6921 = (269256264351160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6921 = 269256264351160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6921 = (14921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6922) ≤ val WuPaper.ClassicalFourthData.Bq 6922
    have hp : val WuPaper.ClassicalFourthData.Bq 6922 = (269262764404312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6922 = 269262764404312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6922 = (7461:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6923) ≤ val WuPaper.ClassicalFourthData.Bq 6923
    have hp : val WuPaper.ClassicalFourthData.Bq 6923 = (269269261339336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6923 = 269269261339336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6923 = (14923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6924) ≤ val WuPaper.ClassicalFourthData.Bq 6924
    have hp : val WuPaper.ClassicalFourthData.Bq 6924 = (269275755157272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6924 = 269275755157272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6924 = (3731:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6925) ≤ val WuPaper.ClassicalFourthData.Bq 6925
    have hp : val WuPaper.ClassicalFourthData.Bq 6925 = (269282245859157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6925 = 269282245859157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6925 = (597:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6926) ≤ val WuPaper.ClassicalFourthData.Bq 6926
    have hp : val WuPaper.ClassicalFourthData.Bq 6926 = (269288733446027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6926 = 269288733446027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6926 = (7463:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6927) ≤ val WuPaper.ClassicalFourthData.Bq 6927
    have hp : val WuPaper.ClassicalFourthData.Bq 6927 = (269295217918921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6927 = 269295217918921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6927 = (14927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_432
