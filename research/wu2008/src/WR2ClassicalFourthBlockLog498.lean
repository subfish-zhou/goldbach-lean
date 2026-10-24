import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints498
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_498 (j : Fin 16) (hj : 16*498+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*498+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*498+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7968) ≤ val WuPaper.ClassicalFourthData.Bq 7968
    have hp : val WuPaper.ClassicalFourthData.Bq 7968 = (274534584197048:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7968 = 274534584197048 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7968 = (499:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7969) ≤ val WuPaper.ClassicalFourthData.Bq 7969
    have hp : val WuPaper.ClassicalFourthData.Bq 7969 = (274538321190740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7969 = 274538321190740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7969 = (15969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7970) ≤ val WuPaper.ClassicalFourthData.Bq 7970
    have hp : val WuPaper.ClassicalFourthData.Bq 7970 = (274542055968037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7970 = 274542055968037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7970 = (1597:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7971) ≤ val WuPaper.ClassicalFourthData.Bq 7971
    have hp : val WuPaper.ClassicalFourthData.Bq 7971 = (274545788529646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7971 = 274545788529646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7971 = (15971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7972) ≤ val WuPaper.ClassicalFourthData.Bq 7972
    have hp : val WuPaper.ClassicalFourthData.Bq 7972 = (274549518876275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7972 = 274549518876275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7972 = (3993:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7973) ≤ val WuPaper.ClassicalFourthData.Bq 7973
    have hp : val WuPaper.ClassicalFourthData.Bq 7973 = (274553247008634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7973 = 274553247008634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7973 = (15973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7974) ≤ val WuPaper.ClassicalFourthData.Bq 7974
    have hp : val WuPaper.ClassicalFourthData.Bq 7974 = (274556972927429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7974 = 274556972927429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7974 = (7987:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7975) ≤ val WuPaper.ClassicalFourthData.Bq 7975
    have hp : val WuPaper.ClassicalFourthData.Bq 7975 = (274560696633367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7975 = 274560696633367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7975 = (639:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7975
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7976) ≤ val WuPaper.ClassicalFourthData.Bq 7976
    have hp : val WuPaper.ClassicalFourthData.Bq 7976 = (274564418127156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7976 = 274564418127156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7976 = (1997:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7977) ≤ val WuPaper.ClassicalFourthData.Bq 7977
    have hp : val WuPaper.ClassicalFourthData.Bq 7977 = (274568137409504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7977 = 274568137409504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7977 = (15977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7978) ≤ val WuPaper.ClassicalFourthData.Bq 7978
    have hp : val WuPaper.ClassicalFourthData.Bq 7978 = (274571854481116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7978 = 274571854481116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7978 = (7989:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7979) ≤ val WuPaper.ClassicalFourthData.Bq 7979
    have hp : val WuPaper.ClassicalFourthData.Bq 7979 = (274575569342699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7979 = 274575569342699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7979 = (15979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7980) ≤ val WuPaper.ClassicalFourthData.Bq 7980
    have hp : val WuPaper.ClassicalFourthData.Bq 7980 = (274579281994959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7980 = 274579281994959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7980 = (799:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7981) ≤ val WuPaper.ClassicalFourthData.Bq 7981
    have hp : val WuPaper.ClassicalFourthData.Bq 7981 = (274582992438602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7981 = 274582992438602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7981 = (15981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7982) ≤ val WuPaper.ClassicalFourthData.Bq 7982
    have hp : val WuPaper.ClassicalFourthData.Bq 7982 = (274586700674334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7982 = 274586700674334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7982 = (7991:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7983) ≤ val WuPaper.ClassicalFourthData.Bq 7983
    have hp : val WuPaper.ClassicalFourthData.Bq 7983 = (274590406702860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7983 = 274590406702860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7983 = (15983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_498
