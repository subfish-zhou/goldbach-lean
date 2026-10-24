import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints570
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_570 (j : Fin 16) (hj : 16*570+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*570+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*570+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9120) ≤ val WuPaper.ClassicalFourthData.Bq 9120
    have hp : val WuPaper.ClassicalFourthData.Bq 9120 = (277533509910782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9120 = 277533509910782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9120 = (107:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9121) ≤ val WuPaper.ClassicalFourthData.Bq 9121
    have hp : val WuPaper.ClassicalFourthData.Bq 9121 = (277535106366643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9121 = 277535106366643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9121 = (17121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9122) ≤ val WuPaper.ClassicalFourthData.Bq 9122
    have hp : val WuPaper.ClassicalFourthData.Bq 9122 = (277536701279049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9122 = 277536701279049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9122 = (8561:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9123) ≤ val WuPaper.ClassicalFourthData.Bq 9123
    have hp : val WuPaper.ClassicalFourthData.Bq 9123 = (277538294648478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9123 = 277538294648478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9123 = (17123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9124) ≤ val WuPaper.ClassicalFourthData.Bq 9124
    have hp : val WuPaper.ClassicalFourthData.Bq 9124 = (277539886475407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9124 = 277539886475407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9124 = (4281:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9125) ≤ val WuPaper.ClassicalFourthData.Bq 9125
    have hp : val WuPaper.ClassicalFourthData.Bq 9125 = (277541476760313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9125 = 277541476760313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9125 = (137:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9126) ≤ val WuPaper.ClassicalFourthData.Bq 9126
    have hp : val WuPaper.ClassicalFourthData.Bq 9126 = (277543065503672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9126 = 277543065503672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9126 = (8563:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9127) ≤ val WuPaper.ClassicalFourthData.Bq 9127
    have hp : val WuPaper.ClassicalFourthData.Bq 9127 = (277544652705961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9127 = 277544652705961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9127 = (17127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9127
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9128) ≤ val WuPaper.ClassicalFourthData.Bq 9128
    have hp : val WuPaper.ClassicalFourthData.Bq 9128 = (277546238367657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9128 = 277546238367657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9128 = (2141:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9129) ≤ val WuPaper.ClassicalFourthData.Bq 9129
    have hp : val WuPaper.ClassicalFourthData.Bq 9129 = (277547822489236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9129 = 277547822489236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9129 = (17129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9130) ≤ val WuPaper.ClassicalFourthData.Bq 9130
    have hp : val WuPaper.ClassicalFourthData.Bq 9130 = (277549405071174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9130 = 277549405071174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9130 = (1713:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9131) ≤ val WuPaper.ClassicalFourthData.Bq 9131
    have hp : val WuPaper.ClassicalFourthData.Bq 9131 = (277550986113947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9131 = 277550986113947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9131 = (17131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9132) ≤ val WuPaper.ClassicalFourthData.Bq 9132
    have hp : val WuPaper.ClassicalFourthData.Bq 9132 = (277552565618030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9132 = 277552565618030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9132 = (4283:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9133) ≤ val WuPaper.ClassicalFourthData.Bq 9133
    have hp : val WuPaper.ClassicalFourthData.Bq 9133 = (277554143583900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9133 = 277554143583900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9133 = (17133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9134) ≤ val WuPaper.ClassicalFourthData.Bq 9134
    have hp : val WuPaper.ClassicalFourthData.Bq 9134 = (277555720012032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9134 = 277555720012032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9134 = (8567:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9135) ≤ val WuPaper.ClassicalFourthData.Bq 9135
    have hp : val WuPaper.ClassicalFourthData.Bq 9135 = (277557294902901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9135 = 277557294902901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9135 = (3427:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_570
