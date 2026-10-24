import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints447
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_447 (j : Fin 16) (hj : 16*447+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*447+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*447+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7152) ≤ val WuPaper.ClassicalFourthData.Bq 7152
    have hp : val WuPaper.ClassicalFourthData.Bq 7152 = (270677004461102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7152 = 270677004461102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7152 = (947:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7153) ≤ val WuPaper.ClassicalFourthData.Bq 7153
    have hp : val WuPaper.ClassicalFourthData.Bq 7153 = (270682811032241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7153 = 270682811032241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7153 = (15153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7154) ≤ val WuPaper.ClassicalFourthData.Bq 7154
    have hp : val WuPaper.ClassicalFourthData.Bq 7154 = (270688614715019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7154 = 270688614715019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7154 = (7577:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7155) ≤ val WuPaper.ClassicalFourthData.Bq 7155
    have hp : val WuPaper.ClassicalFourthData.Bq 7155 = (270694415510388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7155 = 270694415510388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7155 = (3031:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7156) ≤ val WuPaper.ClassicalFourthData.Bq 7156
    have hp : val WuPaper.ClassicalFourthData.Bq 7156 = (270700213419301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7156 = 270700213419301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7156 = (3789:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7157) ≤ val WuPaper.ClassicalFourthData.Bq 7157
    have hp : val WuPaper.ClassicalFourthData.Bq 7157 = (270706008442708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7157 = 270706008442708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7157 = (15157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7158) ≤ val WuPaper.ClassicalFourthData.Bq 7158
    have hp : val WuPaper.ClassicalFourthData.Bq 7158 = (270711800581562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7158 = 270711800581562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7158 = (7579:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7159) ≤ val WuPaper.ClassicalFourthData.Bq 7159
    have hp : val WuPaper.ClassicalFourthData.Bq 7159 = (270717589836811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7159 = 270717589836811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7159 = (15159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7159
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7160) ≤ val WuPaper.ClassicalFourthData.Bq 7160
    have hp : val WuPaper.ClassicalFourthData.Bq 7160 = (270723376209408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7160 = 270723376209408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7160 = (379:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7161) ≤ val WuPaper.ClassicalFourthData.Bq 7161
    have hp : val WuPaper.ClassicalFourthData.Bq 7161 = (270729159700302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7161 = 270729159700302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7161 = (15161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7162) ≤ val WuPaper.ClassicalFourthData.Bq 7162
    have hp : val WuPaper.ClassicalFourthData.Bq 7162 = (270734940310444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7162 = 270734940310444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7162 = (7581:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7163) ≤ val WuPaper.ClassicalFourthData.Bq 7163
    have hp : val WuPaper.ClassicalFourthData.Bq 7163 = (270740718040781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7163 = 270740718040781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7163 = (15163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7164) ≤ val WuPaper.ClassicalFourthData.Bq 7164
    have hp : val WuPaper.ClassicalFourthData.Bq 7164 = (270746492892264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7164 = 270746492892264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7164 = (3791:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7165) ≤ val WuPaper.ClassicalFourthData.Bq 7165
    have hp : val WuPaper.ClassicalFourthData.Bq 7165 = (270752264865841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7165 = 270752264865841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7165 = (3033:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7166) ≤ val WuPaper.ClassicalFourthData.Bq 7166
    have hp : val WuPaper.ClassicalFourthData.Bq 7166 = (270758033962460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7166 = 270758033962460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7166 = (7583:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7167) ≤ val WuPaper.ClassicalFourthData.Bq 7167
    have hp : val WuPaper.ClassicalFourthData.Bq 7167 = (270763800183070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7167 = 270763800183070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7167 = (15167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_447
