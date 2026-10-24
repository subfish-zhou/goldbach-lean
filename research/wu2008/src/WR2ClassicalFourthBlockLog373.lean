import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints373
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_373 (j : Fin 16) (hj : 16*373+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*373+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*373+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5968) ≤ val WuPaper.ClassicalFourthData.Bq 5968
    have hp : val WuPaper.ClassicalFourthData.Bq 5968 = (261479267160717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5968 = 261479267160717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5968 = (873:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5969) ≤ val WuPaper.ClassicalFourthData.Bq 5969
    have hp : val WuPaper.ClassicalFourthData.Bq 5969 = (261489273941067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5969 = 261489273941067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5969 = (13969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5970) ≤ val WuPaper.ClassicalFourthData.Bq 5970
    have hp : val WuPaper.ClassicalFourthData.Bq 5970 = (261499276407694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5970 = 261499276407694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5970 = (1397:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5971) ≤ val WuPaper.ClassicalFourthData.Bq 5971
    have hp : val WuPaper.ClassicalFourthData.Bq 5971 = (261509274562102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5971 = 261509274562102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5971 = (13971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5972) ≤ val WuPaper.ClassicalFourthData.Bq 5972
    have hp : val WuPaper.ClassicalFourthData.Bq 5972 = (261519268405794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5972 = 261519268405794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5972 = (3493:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5973) ≤ val WuPaper.ClassicalFourthData.Bq 5973
    have hp : val WuPaper.ClassicalFourthData.Bq 5973 = (261529257940273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5973 = 261529257940273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5973 = (13973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5974) ≤ val WuPaper.ClassicalFourthData.Bq 5974
    have hp : val WuPaper.ClassicalFourthData.Bq 5974 = (261539243167041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5974 = 261539243167041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5974 = (6987:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5975) ≤ val WuPaper.ClassicalFourthData.Bq 5975
    have hp : val WuPaper.ClassicalFourthData.Bq 5975 = (261549224087600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5975 = 261549224087600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5975 = (559:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5975
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5976) ≤ val WuPaper.ClassicalFourthData.Bq 5976
    have hp : val WuPaper.ClassicalFourthData.Bq 5976 = (261559200703452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5976 = 261559200703452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5976 = (1747:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5977) ≤ val WuPaper.ClassicalFourthData.Bq 5977
    have hp : val WuPaper.ClassicalFourthData.Bq 5977 = (261569173016097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5977 = 261569173016097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5977 = (13977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5978) ≤ val WuPaper.ClassicalFourthData.Bq 5978
    have hp : val WuPaper.ClassicalFourthData.Bq 5978 = (261579141027034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5978 = 261579141027034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5978 = (6989:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5979) ≤ val WuPaper.ClassicalFourthData.Bq 5979
    have hp : val WuPaper.ClassicalFourthData.Bq 5979 = (261589104737764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5979 = 261589104737764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5979 = (13979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5980) ≤ val WuPaper.ClassicalFourthData.Bq 5980
    have hp : val WuPaper.ClassicalFourthData.Bq 5980 = (261599064149785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5980 = 261599064149785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5980 = (699:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5981) ≤ val WuPaper.ClassicalFourthData.Bq 5981
    have hp : val WuPaper.ClassicalFourthData.Bq 5981 = (261609019264595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5981 = 261609019264595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5981 = (13981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5982) ≤ val WuPaper.ClassicalFourthData.Bq 5982
    have hp : val WuPaper.ClassicalFourthData.Bq 5982 = (261618970083692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5982 = 261618970083692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5982 = (6991:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5983) ≤ val WuPaper.ClassicalFourthData.Bq 5983
    have hp : val WuPaper.ClassicalFourthData.Bq 5983 = (261628916608572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5983 = 261628916608572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5983 = (13983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_373
