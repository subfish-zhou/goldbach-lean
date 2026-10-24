import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints380
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_380 (j : Fin 16) (hj : 16*380+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*380+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*380+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6080) ≤ val WuPaper.ClassicalFourthData.Bq 6080
    have hp : val WuPaper.ClassicalFourthData.Bq 6080 = (262573551569135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6080 = 262573551569135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6080 = (88:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6081) ≤ val WuPaper.ClassicalFourthData.Bq 6081
    have hp : val WuPaper.ClassicalFourthData.Bq 6081 = (262583084426372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6081 = 262583084426372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6081 = (14081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6082) ≤ val WuPaper.ClassicalFourthData.Bq 6082
    have hp : val WuPaper.ClassicalFourthData.Bq 6082 = (262592613134660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6082 = 262592613134660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6082 = (7041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6083) ≤ val WuPaper.ClassicalFourthData.Bq 6083
    have hp : val WuPaper.ClassicalFourthData.Bq 6083 = (262602137695437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6083 = 262602137695437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6083 = (14083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6084) ≤ val WuPaper.ClassicalFourthData.Bq 6084
    have hp : val WuPaper.ClassicalFourthData.Bq 6084 = (262611658110141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6084 = 262611658110141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6084 = (3521:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6085) ≤ val WuPaper.ClassicalFourthData.Bq 6085
    have hp : val WuPaper.ClassicalFourthData.Bq 6085 = (262621174380208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6085 = 262621174380208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6085 = (2817:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6086) ≤ val WuPaper.ClassicalFourthData.Bq 6086
    have hp : val WuPaper.ClassicalFourthData.Bq 6086 = (262630686507075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6086 = 262630686507075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6086 = (7043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6087) ≤ val WuPaper.ClassicalFourthData.Bq 6087
    have hp : val WuPaper.ClassicalFourthData.Bq 6087 = (262640194492179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6087 = 262640194492179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6087 = (14087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6087
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6088) ≤ val WuPaper.ClassicalFourthData.Bq 6088
    have hp : val WuPaper.ClassicalFourthData.Bq 6088 = (262649698336954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6088 = 262649698336954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6088 = (1761:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6089) ≤ val WuPaper.ClassicalFourthData.Bq 6089
    have hp : val WuPaper.ClassicalFourthData.Bq 6089 = (262659198042835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6089 = 262659198042835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6089 = (14089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6090) ≤ val WuPaper.ClassicalFourthData.Bq 6090
    have hp : val WuPaper.ClassicalFourthData.Bq 6090 = (262668693611256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6090 = 262668693611256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6090 = (1409:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6091) ≤ val WuPaper.ClassicalFourthData.Bq 6091
    have hp : val WuPaper.ClassicalFourthData.Bq 6091 = (262678185043652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6091 = 262678185043652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6091 = (14091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6092) ≤ val WuPaper.ClassicalFourthData.Bq 6092
    have hp : val WuPaper.ClassicalFourthData.Bq 6092 = (262687672341454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6092 = 262687672341454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6092 = (3523:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6093) ≤ val WuPaper.ClassicalFourthData.Bq 6093
    have hp : val WuPaper.ClassicalFourthData.Bq 6093 = (262697155506097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6093 = 262697155506097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6093 = (14093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6094) ≤ val WuPaper.ClassicalFourthData.Bq 6094
    have hp : val WuPaper.ClassicalFourthData.Bq 6094 = (262706634539010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6094 = 262706634539010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6094 = (7047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6095) ≤ val WuPaper.ClassicalFourthData.Bq 6095
    have hp : val WuPaper.ClassicalFourthData.Bq 6095 = (262716109441627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6095 = 262716109441627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6095 = (2819:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_380
