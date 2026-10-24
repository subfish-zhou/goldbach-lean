import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints571
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_571 (j : Fin 16) (hj : 16*571+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*571+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*571+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9136) ≤ val WuPaper.ClassicalFourthData.Bq 9136
    have hp : val WuPaper.ClassicalFourthData.Bq 9136 = (277558868256982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9136 = 277558868256982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9136 = (1071:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9137) ≤ val WuPaper.ClassicalFourthData.Bq 9137
    have hp : val WuPaper.ClassicalFourthData.Bq 9137 = (277560440074750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9137 = 277560440074750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9137 = (17137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9138) ≤ val WuPaper.ClassicalFourthData.Bq 9138
    have hp : val WuPaper.ClassicalFourthData.Bq 9138 = (277562010356681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9138 = 277562010356681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9138 = (8569:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9139) ≤ val WuPaper.ClassicalFourthData.Bq 9139
    have hp : val WuPaper.ClassicalFourthData.Bq 9139 = (277563579103248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9139 = 277563579103248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9139 = (17139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9140) ≤ val WuPaper.ClassicalFourthData.Bq 9140
    have hp : val WuPaper.ClassicalFourthData.Bq 9140 = (277565146314927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9140 = 277565146314927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9140 = (857:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9141) ≤ val WuPaper.ClassicalFourthData.Bq 9141
    have hp : val WuPaper.ClassicalFourthData.Bq 9141 = (277566711992192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9141 = 277566711992192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9141 = (17141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9142) ≤ val WuPaper.ClassicalFourthData.Bq 9142
    have hp : val WuPaper.ClassicalFourthData.Bq 9142 = (277568276135516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9142 = 277568276135516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9142 = (8571:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9143) ≤ val WuPaper.ClassicalFourthData.Bq 9143
    have hp : val WuPaper.ClassicalFourthData.Bq 9143 = (277569838745375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9143 = 277569838745375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9143 = (17143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9143
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9144) ≤ val WuPaper.ClassicalFourthData.Bq 9144
    have hp : val WuPaper.ClassicalFourthData.Bq 9144 = (277571399822242:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9144 = 277571399822242 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9144 = (2143:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9145) ≤ val WuPaper.ClassicalFourthData.Bq 9145
    have hp : val WuPaper.ClassicalFourthData.Bq 9145 = (277572959366590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9145 = 277572959366590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9145 = (3429:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9146) ≤ val WuPaper.ClassicalFourthData.Bq 9146
    have hp : val WuPaper.ClassicalFourthData.Bq 9146 = (277574517378893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9146 = 277574517378893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9146 = (8573:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9147) ≤ val WuPaper.ClassicalFourthData.Bq 9147
    have hp : val WuPaper.ClassicalFourthData.Bq 9147 = (277576073859626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9147 = 277576073859626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9147 = (17147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9148) ≤ val WuPaper.ClassicalFourthData.Bq 9148
    have hp : val WuPaper.ClassicalFourthData.Bq 9148 = (277577628809260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9148 = 277577628809260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9148 = (4287:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9149) ≤ val WuPaper.ClassicalFourthData.Bq 9149
    have hp : val WuPaper.ClassicalFourthData.Bq 9149 = (277579182228269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9149 = 277579182228269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9149 = (17149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9150) ≤ val WuPaper.ClassicalFourthData.Bq 9150
    have hp : val WuPaper.ClassicalFourthData.Bq 9150 = (277580734117126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9150 = 277580734117126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9150 = (343:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9151) ≤ val WuPaper.ClassicalFourthData.Bq 9151
    have hp : val WuPaper.ClassicalFourthData.Bq 9151 = (277582284476304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9151 = 277582284476304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9151 = (17151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_571
