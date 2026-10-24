import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints069
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_069 (j : Fin 16) (hj : 16*69+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*69+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*69+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1104) ≤ val WuPaper.ClassicalFourthData.Bq 1104
    have hp : val WuPaper.ClassicalFourthData.Bq 1104 = (107087075976537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1104 = 107087075976537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1104 = (569:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1105) ≤ val WuPaper.ClassicalFourthData.Bq 1105
    have hp : val WuPaper.ClassicalFourthData.Bq 1105 = (107161379680061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1105 = 107161379680061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1105 = (1821:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1106) ≤ val WuPaper.ClassicalFourthData.Bq 1106
    have hp : val WuPaper.ClassicalFourthData.Bq 1106 = (107235650208391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1106 = 107235650208391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1106 = (4553:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1107) ≤ val WuPaper.ClassicalFourthData.Bq 1107
    have hp : val WuPaper.ClassicalFourthData.Bq 1107 = (107309887579057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1107 = 107309887579057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1107 = (9107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1108) ≤ val WuPaper.ClassicalFourthData.Bq 1108
    have hp : val WuPaper.ClassicalFourthData.Bq 1108 = (107384091809575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1108 = 107384091809575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1108 = (2277:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1109) ≤ val WuPaper.ClassicalFourthData.Bq 1109
    have hp : val WuPaper.ClassicalFourthData.Bq 1109 = (107458262917454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1109 = 107458262917454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1109 = (9109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1110) ≤ val WuPaper.ClassicalFourthData.Bq 1110
    have hp : val WuPaper.ClassicalFourthData.Bq 1110 = (107532400920186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1110 = 107532400920186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1110 = (911:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1111) ≤ val WuPaper.ClassicalFourthData.Bq 1111
    have hp : val WuPaper.ClassicalFourthData.Bq 1111 = (107606505835255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1111 = 107606505835255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1111 = (9111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1111
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1112) ≤ val WuPaper.ClassicalFourthData.Bq 1112
    have hp : val WuPaper.ClassicalFourthData.Bq 1112 = (107680577680134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1112 = 107680577680134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1112 = (1139:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1113) ≤ val WuPaper.ClassicalFourthData.Bq 1113
    have hp : val WuPaper.ClassicalFourthData.Bq 1113 = (107754616472280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1113 = 107754616472280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1113 = (9113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1114) ≤ val WuPaper.ClassicalFourthData.Bq 1114
    have hp : val WuPaper.ClassicalFourthData.Bq 1114 = (107828622229144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1114 = 107828622229144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1114 = (4557:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1115) ≤ val WuPaper.ClassicalFourthData.Bq 1115
    have hp : val WuPaper.ClassicalFourthData.Bq 1115 = (107902594968163:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1115 = 107902594968163 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1115 = (1823:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1116) ≤ val WuPaper.ClassicalFourthData.Bq 1116
    have hp : val WuPaper.ClassicalFourthData.Bq 1116 = (107976534706760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1116 = 107976534706760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1116 = (2279:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1117) ≤ val WuPaper.ClassicalFourthData.Bq 1117
    have hp : val WuPaper.ClassicalFourthData.Bq 1117 = (108050441462352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1117 = 108050441462352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1117 = (9117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1118) ≤ val WuPaper.ClassicalFourthData.Bq 1118
    have hp : val WuPaper.ClassicalFourthData.Bq 1118 = (108124315252339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1118 = 108124315252339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1118 = (4559:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1119) ≤ val WuPaper.ClassicalFourthData.Bq 1119
    have hp : val WuPaper.ClassicalFourthData.Bq 1119 = (108198156094114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1119 = 108198156094114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1119 = (9119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_069
