import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints445
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_445 (j : Fin 16) (hj : 16*445+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*445+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*445+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7120) ≤ val WuPaper.ClassicalFourthData.Bq 7120
    have hp : val WuPaper.ClassicalFourthData.Bq 7120 = (270489663413464:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7120 = 270489663413464 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7120 = (189:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7121) ≤ val WuPaper.ClassicalFourthData.Bq 7121
    have hp : val WuPaper.ClassicalFourthData.Bq 7121 = (270495562917046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7121 = 270495562917046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7121 = (15121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7122) ≤ val WuPaper.ClassicalFourthData.Bq 7122
    have hp : val WuPaper.ClassicalFourthData.Bq 7122 = (270501459501609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7122 = 270501459501609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7122 = (7561:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7123) ≤ val WuPaper.ClassicalFourthData.Bq 7123
    have hp : val WuPaper.ClassicalFourthData.Bq 7123 = (270507353168115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7123 = 270507353168115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7123 = (15123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7124) ≤ val WuPaper.ClassicalFourthData.Bq 7124
    have hp : val WuPaper.ClassicalFourthData.Bq 7124 = (270513243917530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7124 = 270513243917530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7124 = (3781:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7125) ≤ val WuPaper.ClassicalFourthData.Bq 7125
    have hp : val WuPaper.ClassicalFourthData.Bq 7125 = (270519131750814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7125 = 270519131750814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7125 = (121:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7126) ≤ val WuPaper.ClassicalFourthData.Bq 7126
    have hp : val WuPaper.ClassicalFourthData.Bq 7126 = (270525016668931:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7126 = 270525016668931 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7126 = (7563:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7127) ≤ val WuPaper.ClassicalFourthData.Bq 7127
    have hp : val WuPaper.ClassicalFourthData.Bq 7127 = (270530898672844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7127 = 270530898672844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7127 = (15127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7127
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7128) ≤ val WuPaper.ClassicalFourthData.Bq 7128
    have hp : val WuPaper.ClassicalFourthData.Bq 7128 = (270536777763513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7128 = 270536777763513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7128 = (1891:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7129) ≤ val WuPaper.ClassicalFourthData.Bq 7129
    have hp : val WuPaper.ClassicalFourthData.Bq 7129 = (270542653941900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7129 = 270542653941900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7129 = (15129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7130) ≤ val WuPaper.ClassicalFourthData.Bq 7130
    have hp : val WuPaper.ClassicalFourthData.Bq 7130 = (270548527208967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7130 = 270548527208967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7130 = (1513:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7131) ≤ val WuPaper.ClassicalFourthData.Bq 7131
    have hp : val WuPaper.ClassicalFourthData.Bq 7131 = (270554397565675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7131 = 270554397565675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7131 = (15131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7132) ≤ val WuPaper.ClassicalFourthData.Bq 7132
    have hp : val WuPaper.ClassicalFourthData.Bq 7132 = (270560265012982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7132 = 270560265012982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7132 = (3783:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7133) ≤ val WuPaper.ClassicalFourthData.Bq 7133
    have hp : val WuPaper.ClassicalFourthData.Bq 7133 = (270566129551851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7133 = 270566129551851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7133 = (15133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7134) ≤ val WuPaper.ClassicalFourthData.Bq 7134
    have hp : val WuPaper.ClassicalFourthData.Bq 7134 = (270571991183239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7134 = 270571991183239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7134 = (7567:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7135) ≤ val WuPaper.ClassicalFourthData.Bq 7135
    have hp : val WuPaper.ClassicalFourthData.Bq 7135 = (270577849908107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7135 = 270577849908107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7135 = (3027:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_445
