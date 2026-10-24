import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints366
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_366 (j : Fin 16) (hj : 16*366+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*366+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*366+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5856) ≤ val WuPaper.ClassicalFourthData.Bq 5856
    have hp : val WuPaper.ClassicalFourthData.Bq 5856 = (260330844593327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5856 = 260330844593327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5856 = (433:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5857) ≤ val WuPaper.ClassicalFourthData.Bq 5857
    have hp : val WuPaper.ClassicalFourthData.Bq 5857 = (260341344176495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5857 = 260341344176495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5857 = (13857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5858) ≤ val WuPaper.ClassicalFourthData.Bq 5858
    have hp : val WuPaper.ClassicalFourthData.Bq 5858 = (260351839273577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5858 = 260351839273577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5858 = (6929:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5859) ≤ val WuPaper.ClassicalFourthData.Bq 5859
    have hp : val WuPaper.ClassicalFourthData.Bq 5859 = (260362329886146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5859 = 260362329886146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5859 = (13859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5860) ≤ val WuPaper.ClassicalFourthData.Bq 5860
    have hp : val WuPaper.ClassicalFourthData.Bq 5860 = (260372816015777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5860 = 260372816015777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5860 = (693:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5861) ≤ val WuPaper.ClassicalFourthData.Bq 5861
    have hp : val WuPaper.ClassicalFourthData.Bq 5861 = (260383297664040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5861 = 260383297664040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5861 = (13861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5862) ≤ val WuPaper.ClassicalFourthData.Bq 5862
    have hp : val WuPaper.ClassicalFourthData.Bq 5862 = (260393774832508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5862 = 260393774832508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5862 = (6931:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5863) ≤ val WuPaper.ClassicalFourthData.Bq 5863
    have hp : val WuPaper.ClassicalFourthData.Bq 5863 = (260404247522752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5863 = 260404247522752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5863 = (13863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5863
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5864) ≤ val WuPaper.ClassicalFourthData.Bq 5864
    have hp : val WuPaper.ClassicalFourthData.Bq 5864 = (260414715736343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5864 = 260414715736343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5864 = (1733:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5865) ≤ val WuPaper.ClassicalFourthData.Bq 5865
    have hp : val WuPaper.ClassicalFourthData.Bq 5865 = (260425179474850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5865 = 260425179474850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5865 = (2773:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5866) ≤ val WuPaper.ClassicalFourthData.Bq 5866
    have hp : val WuPaper.ClassicalFourthData.Bq 5866 = (260435638739844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5866 = 260435638739844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5866 = (6933:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5867) ≤ val WuPaper.ClassicalFourthData.Bq 5867
    have hp : val WuPaper.ClassicalFourthData.Bq 5867 = (260446093532891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5867 = 260446093532891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5867 = (13867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5868) ≤ val WuPaper.ClassicalFourthData.Bq 5868
    have hp : val WuPaper.ClassicalFourthData.Bq 5868 = (260456543855562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5868 = 260456543855562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5868 = (3467:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5869) ≤ val WuPaper.ClassicalFourthData.Bq 5869
    have hp : val WuPaper.ClassicalFourthData.Bq 5869 = (260466989709422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5869 = 260466989709422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5869 = (13869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5870) ≤ val WuPaper.ClassicalFourthData.Bq 5870
    have hp : val WuPaper.ClassicalFourthData.Bq 5870 = (260477431096038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5870 = 260477431096038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5870 = (1387:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5871) ≤ val WuPaper.ClassicalFourthData.Bq 5871
    have hp : val WuPaper.ClassicalFourthData.Bq 5871 = (260487868016977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5871 = 260487868016977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5871 = (13871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_366
