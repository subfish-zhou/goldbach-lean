import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints435
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_435 (j : Fin 16) (hj : 16*435+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*435+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*435+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6960) ≤ val WuPaper.ClassicalFourthData.Bq 6960
    have hp : val WuPaper.ClassicalFourthData.Bq 6960 = (269507465347651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6960 = 269507465347651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6960 = (187:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6961) ≤ val WuPaper.ClassicalFourthData.Bq 6961
    have hp : val WuPaper.ClassicalFourthData.Bq 6961 = (269513844559570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6961 = 269513844559570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6961 = (14961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6962) ≤ val WuPaper.ClassicalFourthData.Bq 6962
    have hp : val WuPaper.ClassicalFourthData.Bq 6962 = (269520220693562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6962 = 269520220693562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6962 = (7481:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6963) ≤ val WuPaper.ClassicalFourthData.Bq 6963
    have hp : val WuPaper.ClassicalFourthData.Bq 6963 = (269526593750651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6963 = 269526593750651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6963 = (14963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6964) ≤ val WuPaper.ClassicalFourthData.Bq 6964
    have hp : val WuPaper.ClassicalFourthData.Bq 6964 = (269532963731859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6964 = 269532963731859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6964 = (3741:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6965) ≤ val WuPaper.ClassicalFourthData.Bq 6965
    have hp : val WuPaper.ClassicalFourthData.Bq 6965 = (269539330638209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6965 = 269539330638209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6965 = (2993:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6966) ≤ val WuPaper.ClassicalFourthData.Bq 6966
    have hp : val WuPaper.ClassicalFourthData.Bq 6966 = (269545694470721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6966 = 269545694470721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6966 = (7483:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6967) ≤ val WuPaper.ClassicalFourthData.Bq 6967
    have hp : val WuPaper.ClassicalFourthData.Bq 6967 = (269552055230419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6967 = 269552055230419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6967 = (14967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6967
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6968) ≤ val WuPaper.ClassicalFourthData.Bq 6968
    have hp : val WuPaper.ClassicalFourthData.Bq 6968 = (269558412918322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6968 = 269558412918322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6968 = (1871:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6969) ≤ val WuPaper.ClassicalFourthData.Bq 6969
    have hp : val WuPaper.ClassicalFourthData.Bq 6969 = (269564767535452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6969 = 269564767535452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6969 = (14969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6970) ≤ val WuPaper.ClassicalFourthData.Bq 6970
    have hp : val WuPaper.ClassicalFourthData.Bq 6970 = (269571119082829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6970 = 269571119082829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6970 = (1497:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6971) ≤ val WuPaper.ClassicalFourthData.Bq 6971
    have hp : val WuPaper.ClassicalFourthData.Bq 6971 = (269577467561473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6971 = 269577467561473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6971 = (14971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6972) ≤ val WuPaper.ClassicalFourthData.Bq 6972
    have hp : val WuPaper.ClassicalFourthData.Bq 6972 = (269583812972404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6972 = 269583812972404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6972 = (3743:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6973) ≤ val WuPaper.ClassicalFourthData.Bq 6973
    have hp : val WuPaper.ClassicalFourthData.Bq 6973 = (269590155316640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6973 = 269590155316640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6973 = (14973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6974) ≤ val WuPaper.ClassicalFourthData.Bq 6974
    have hp : val WuPaper.ClassicalFourthData.Bq 6974 = (269596494595201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6974 = 269596494595201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6974 = (7487:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6975) ≤ val WuPaper.ClassicalFourthData.Bq 6975
    have hp : val WuPaper.ClassicalFourthData.Bq 6975 = (269602830809105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6975 = 269602830809105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6975 = (599:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_435
