import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints249
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_249 (j : Fin 16) (hj : 16*249+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*249+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*249+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3984) ≤ val WuPaper.ClassicalFourthData.Bq 3984
    have hp : val WuPaper.ClassicalFourthData.Bq 3984 = (230689311712041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3984 = 230689311712041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3984 = (749:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3985) ≤ val WuPaper.ClassicalFourthData.Bq 3985
    have hp : val WuPaper.ClassicalFourthData.Bq 3985 = (230711863344877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3985 = 230711863344877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3985 = (2397:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3986) ≤ val WuPaper.ClassicalFourthData.Bq 3986
    have hp : val WuPaper.ClassicalFourthData.Bq 3986 = (230734405980691:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3986 = 230734405980691 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3986 = (5993:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3987) ≤ val WuPaper.ClassicalFourthData.Bq 3987
    have hp : val WuPaper.ClassicalFourthData.Bq 3987 = (230756939623046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3987 = 230756939623046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3987 = (11987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3988) ≤ val WuPaper.ClassicalFourthData.Bq 3988
    have hp : val WuPaper.ClassicalFourthData.Bq 3988 = (230779464275502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3988 = 230779464275502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3988 = (2997:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3989) ≤ val WuPaper.ClassicalFourthData.Bq 3989
    have hp : val WuPaper.ClassicalFourthData.Bq 3989 = (230801979941618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3989 = 230801979941618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3989 = (11989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3990) ≤ val WuPaper.ClassicalFourthData.Bq 3990
    have hp : val WuPaper.ClassicalFourthData.Bq 3990 = (230824486624952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3990 = 230824486624952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3990 = (1199:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3991) ≤ val WuPaper.ClassicalFourthData.Bq 3991
    have hp : val WuPaper.ClassicalFourthData.Bq 3991 = (230846984329059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3991 = 230846984329059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3991 = (11991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3991
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3992) ≤ val WuPaper.ClassicalFourthData.Bq 3992
    have hp : val WuPaper.ClassicalFourthData.Bq 3992 = (230869473057493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3992 = 230869473057493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3992 = (1499:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3993) ≤ val WuPaper.ClassicalFourthData.Bq 3993
    have hp : val WuPaper.ClassicalFourthData.Bq 3993 = (230891952813806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3993 = 230891952813806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3993 = (11993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3994) ≤ val WuPaper.ClassicalFourthData.Bq 3994
    have hp : val WuPaper.ClassicalFourthData.Bq 3994 = (230914423601548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3994 = 230914423601548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3994 = (5997:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3995) ≤ val WuPaper.ClassicalFourthData.Bq 3995
    have hp : val WuPaper.ClassicalFourthData.Bq 3995 = (230936885424270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3995 = 230936885424270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3995 = (2399:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3996) ≤ val WuPaper.ClassicalFourthData.Bq 3996
    have hp : val WuPaper.ClassicalFourthData.Bq 3996 = (230959338285517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3996 = 230959338285517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3996 = (2999:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3997) ≤ val WuPaper.ClassicalFourthData.Bq 3997
    have hp : val WuPaper.ClassicalFourthData.Bq 3997 = (230981782188835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3997 = 230981782188835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3997 = (11997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3998) ≤ val WuPaper.ClassicalFourthData.Bq 3998
    have hp : val WuPaper.ClassicalFourthData.Bq 3998 = (231004217137769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3998 = 231004217137769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3998 = (5999:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3999) ≤ val WuPaper.ClassicalFourthData.Bq 3999
    have hp : val WuPaper.ClassicalFourthData.Bq 3999 = (231026643135860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3999 = 231026643135860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3999 = (11999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_249
