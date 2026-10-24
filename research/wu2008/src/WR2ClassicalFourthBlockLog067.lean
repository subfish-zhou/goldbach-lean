import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints067
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_067 (j : Fin 16) (hj : 16*67+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*67+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*67+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1072) ≤ val WuPaper.ClassicalFourthData.Bq 1072
    have hp : val WuPaper.ClassicalFourthData.Bq 1072 = (104691735456365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1072 = 104691735456365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1072 = (567:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1073) ≤ val WuPaper.ClassicalFourthData.Bq 1073
    have hp : val WuPaper.ClassicalFourthData.Bq 1073 = (104767110091332:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1073 = 104767110091332 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1073 = (9073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1074) ≤ val WuPaper.ClassicalFourthData.Bq 1074
    have hp : val WuPaper.ClassicalFourthData.Bq 1074 = (104842450983999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1074 = 104842450983999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1074 = (4537:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1075) ≤ val WuPaper.ClassicalFourthData.Bq 1075
    have hp : val WuPaper.ClassicalFourthData.Bq 1075 = (104917758152270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1075 = 104917758152270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1075 = (363:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1076) ≤ val WuPaper.ClassicalFourthData.Bq 1076
    have hp : val WuPaper.ClassicalFourthData.Bq 1076 = (104993031614038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1076 = 104993031614038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1076 = (2269:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1077) ≤ val WuPaper.ClassicalFourthData.Bq 1077
    have hp : val WuPaper.ClassicalFourthData.Bq 1077 = (105068271387184:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1077 = 105068271387184 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1077 = (9077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1078) ≤ val WuPaper.ClassicalFourthData.Bq 1078
    have hp : val WuPaper.ClassicalFourthData.Bq 1078 = (105143477489578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1078 = 105143477489578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1078 = (4539:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1079) ≤ val WuPaper.ClassicalFourthData.Bq 1079
    have hp : val WuPaper.ClassicalFourthData.Bq 1079 = (105218649939076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1079 = 105218649939076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1079 = (9079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1079
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1080) ≤ val WuPaper.ClassicalFourthData.Bq 1080
    have hp : val WuPaper.ClassicalFourthData.Bq 1080 = (105293788753525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1080 = 105293788753525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1080 = (227:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1081) ≤ val WuPaper.ClassicalFourthData.Bq 1081
    have hp : val WuPaper.ClassicalFourthData.Bq 1081 = (105368893950757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1081 = 105368893950757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1081 = (9081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1082) ≤ val WuPaper.ClassicalFourthData.Bq 1082
    have hp : val WuPaper.ClassicalFourthData.Bq 1082 = (105443965548594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1082 = 105443965548594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1082 = (4541:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1083) ≤ val WuPaper.ClassicalFourthData.Bq 1083
    have hp : val WuPaper.ClassicalFourthData.Bq 1083 = (105519003564847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1083 = 105519003564847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1083 = (9083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1084) ≤ val WuPaper.ClassicalFourthData.Bq 1084
    have hp : val WuPaper.ClassicalFourthData.Bq 1084 = (105594008017313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1084 = 105594008017313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1084 = (2271:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1085) ≤ val WuPaper.ClassicalFourthData.Bq 1085
    have hp : val WuPaper.ClassicalFourthData.Bq 1085 = (105668978923779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1085 = 105668978923779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1085 = (1817:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1086) ≤ val WuPaper.ClassicalFourthData.Bq 1086
    have hp : val WuPaper.ClassicalFourthData.Bq 1086 = (105743916302020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1086 = 105743916302020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1086 = (4543:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1087) ≤ val WuPaper.ClassicalFourthData.Bq 1087
    have hp : val WuPaper.ClassicalFourthData.Bq 1087 = (105818820169798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1087 = 105818820169798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1087 = (9087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_067
