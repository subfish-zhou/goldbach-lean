import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints311
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_311 (j : Fin 16) (hj : 16*311+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*311+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*311+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4976) ≤ val WuPaper.ClassicalFourthData.Bq 4976
    have hp : val WuPaper.ClassicalFourthData.Bq 4976 = (249155359944652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4976 = 249155359944652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4976 = (811:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4977) ≤ val WuPaper.ClassicalFourthData.Bq 4977
    have hp : val WuPaper.ClassicalFourthData.Bq 4977 = (249170498467955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4977 = 249170498467955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4977 = (12977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4978) ≤ val WuPaper.ClassicalFourthData.Bq 4978
    have hp : val WuPaper.ClassicalFourthData.Bq 4978 = (249185630833673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4978 = 249185630833673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4978 = (6489:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4979) ≤ val WuPaper.ClassicalFourthData.Bq 4979
    have hp : val WuPaper.ClassicalFourthData.Bq 4979 = (249200757044081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4979 = 249200757044081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4979 = (12979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4980) ≤ val WuPaper.ClassicalFourthData.Bq 4980
    have hp : val WuPaper.ClassicalFourthData.Bq 4980 = (249215877101454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4980 = 249215877101454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4980 = (649:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4981) ≤ val WuPaper.ClassicalFourthData.Bq 4981
    have hp : val WuPaper.ClassicalFourthData.Bq 4981 = (249230991008065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4981 = 249230991008065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4981 = (12981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4982) ≤ val WuPaper.ClassicalFourthData.Bq 4982
    have hp : val WuPaper.ClassicalFourthData.Bq 4982 = (249246098766186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4982 = 249246098766186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4982 = (6491:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4983) ≤ val WuPaper.ClassicalFourthData.Bq 4983
    have hp : val WuPaper.ClassicalFourthData.Bq 4983 = (249261200378089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4983 = 249261200378089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4983 = (12983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4983
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4984) ≤ val WuPaper.ClassicalFourthData.Bq 4984
    have hp : val WuPaper.ClassicalFourthData.Bq 4984 = (249276295846042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4984 = 249276295846042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4984 = (1623:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4985) ≤ val WuPaper.ClassicalFourthData.Bq 4985
    have hp : val WuPaper.ClassicalFourthData.Bq 4985 = (249291385172317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4985 = 249291385172317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4985 = (2597:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4986) ≤ val WuPaper.ClassicalFourthData.Bq 4986
    have hp : val WuPaper.ClassicalFourthData.Bq 4986 = (249306468359181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4986 = 249306468359181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4986 = (6493:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4987) ≤ val WuPaper.ClassicalFourthData.Bq 4987
    have hp : val WuPaper.ClassicalFourthData.Bq 4987 = (249321545408901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4987 = 249321545408901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4987 = (12987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4988) ≤ val WuPaper.ClassicalFourthData.Bq 4988
    have hp : val WuPaper.ClassicalFourthData.Bq 4988 = (249336616323743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4988 = 249336616323743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4988 = (3247:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4989) ≤ val WuPaper.ClassicalFourthData.Bq 4989
    have hp : val WuPaper.ClassicalFourthData.Bq 4989 = (249351681105974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4989 = 249351681105974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4989 = (12989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4990) ≤ val WuPaper.ClassicalFourthData.Bq 4990
    have hp : val WuPaper.ClassicalFourthData.Bq 4990 = (249366739757857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4990 = 249366739757857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4990 = (1299:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4991) ≤ val WuPaper.ClassicalFourthData.Bq 4991
    have hp : val WuPaper.ClassicalFourthData.Bq 4991 = (249381792281656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4991 = 249381792281656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4991 = (12991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4991
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_311
