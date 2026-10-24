import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints181
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_181 (j : Fin 16) (hj : 16*181+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*181+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*181+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2896) ≤ val WuPaper.ClassicalFourthData.Bq 2896
    have hp : val WuPaper.ClassicalFourthData.Bq 2896 = (199943895830214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2896 = 199943895830214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2896 = (681:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2897) ≤ val WuPaper.ClassicalFourthData.Bq 2897
    have hp : val WuPaper.ClassicalFourthData.Bq 2897 = (199978773361206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2897 = 199978773361206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2897 = (10897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2898) ≤ val WuPaper.ClassicalFourthData.Bq 2898
    have hp : val WuPaper.ClassicalFourthData.Bq 2898 = (200013636775467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2898 = 200013636775467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2898 = (5449:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2899) ≤ val WuPaper.ClassicalFourthData.Bq 2899
    have hp : val WuPaper.ClassicalFourthData.Bq 2899 = (200048486079120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2899 = 200048486079120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2899 = (10899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2900) ≤ val WuPaper.ClassicalFourthData.Bq 2900
    have hp : val WuPaper.ClassicalFourthData.Bq 2900 = (200083321278284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2900 = 200083321278284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2900 = (109:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2901) ≤ val WuPaper.ClassicalFourthData.Bq 2901
    have hp : val WuPaper.ClassicalFourthData.Bq 2901 = (200118142379076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2901 = 200118142379076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2901 = (10901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2902) ≤ val WuPaper.ClassicalFourthData.Bq 2902
    have hp : val WuPaper.ClassicalFourthData.Bq 2902 = (200152949387607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2902 = 200152949387607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2902 = (5451:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2903) ≤ val WuPaper.ClassicalFourthData.Bq 2903
    have hp : val WuPaper.ClassicalFourthData.Bq 2903 = (200187742309988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2903 = 200187742309988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2903 = (10903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2903
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2904) ≤ val WuPaper.ClassicalFourthData.Bq 2904
    have hp : val WuPaper.ClassicalFourthData.Bq 2904 = (200222521152325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2904 = 200222521152325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2904 = (1363:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2905) ≤ val WuPaper.ClassicalFourthData.Bq 2905
    have hp : val WuPaper.ClassicalFourthData.Bq 2905 = (200257285920721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2905 = 200257285920721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2905 = (2181:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2906) ≤ val WuPaper.ClassicalFourthData.Bq 2906
    have hp : val WuPaper.ClassicalFourthData.Bq 2906 = (200292036621277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2906 = 200292036621277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2906 = (5453:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2907) ≤ val WuPaper.ClassicalFourthData.Bq 2907
    have hp : val WuPaper.ClassicalFourthData.Bq 2907 = (200326773260089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2907 = 200326773260089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2907 = (10907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2908) ≤ val WuPaper.ClassicalFourthData.Bq 2908
    have hp : val WuPaper.ClassicalFourthData.Bq 2908 = (200361495843250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2908 = 200361495843250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2908 = (2727:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2909) ≤ val WuPaper.ClassicalFourthData.Bq 2909
    have hp : val WuPaper.ClassicalFourthData.Bq 2909 = (200396204376852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2909 = 200396204376852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2909 = (10909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2910) ≤ val WuPaper.ClassicalFourthData.Bq 2910
    have hp : val WuPaper.ClassicalFourthData.Bq 2910 = (200430898866980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2910 = 200430898866980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2910 = (1091:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2911) ≤ val WuPaper.ClassicalFourthData.Bq 2911
    have hp : val WuPaper.ClassicalFourthData.Bq 2911 = (200465579319721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2911 = 200465579319721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2911 = (10911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_181
