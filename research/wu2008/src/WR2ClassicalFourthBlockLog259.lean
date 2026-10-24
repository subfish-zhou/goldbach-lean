import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints259
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_259 (j : Fin 16) (hj : 16*259+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*259+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*259+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4144) ≤ val WuPaper.ClassicalFourthData.Bq 4144
    have hp : val WuPaper.ClassicalFourthData.Bq 4144 = (234185473876244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4144 = 234185473876244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4144 = (759:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4145) ≤ val WuPaper.ClassicalFourthData.Bq 4145
    have hp : val WuPaper.ClassicalFourthData.Bq 4145 = (234206630196499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4145 = 234206630196499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4145 = (2429:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4146) ≤ val WuPaper.ClassicalFourthData.Bq 4146
    have hp : val WuPaper.ClassicalFourthData.Bq 4146 = (234227778068938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4146 = 234227778068938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4146 = (6073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4147) ≤ val WuPaper.ClassicalFourthData.Bq 4147
    have hp : val WuPaper.ClassicalFourthData.Bq 4147 = (234248917496869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4147 = 234248917496869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4147 = (12147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4148) ≤ val WuPaper.ClassicalFourthData.Bq 4148
    have hp : val WuPaper.ClassicalFourthData.Bq 4148 = (234270048483592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4148 = 234270048483592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4148 = (3037:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4149) ≤ val WuPaper.ClassicalFourthData.Bq 4149
    have hp : val WuPaper.ClassicalFourthData.Bq 4149 = (234291171032412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4149 = 234291171032412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4149 = (12149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4150) ≤ val WuPaper.ClassicalFourthData.Bq 4150
    have hp : val WuPaper.ClassicalFourthData.Bq 4150 = (234312285146628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4150 = 234312285146628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4150 = (243:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4151) ≤ val WuPaper.ClassicalFourthData.Bq 4151
    have hp : val WuPaper.ClassicalFourthData.Bq 4151 = (234333390829539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4151 = 234333390829539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4151 = (12151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4152) ≤ val WuPaper.ClassicalFourthData.Bq 4152
    have hp : val WuPaper.ClassicalFourthData.Bq 4152 = (234354488084442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4152 = 234354488084442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4152 = (1519:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4153) ≤ val WuPaper.ClassicalFourthData.Bq 4153
    have hp : val WuPaper.ClassicalFourthData.Bq 4153 = (234375576914633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4153 = 234375576914633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4153 = (12153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4154) ≤ val WuPaper.ClassicalFourthData.Bq 4154
    have hp : val WuPaper.ClassicalFourthData.Bq 4154 = (234396657323407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4154 = 234396657323407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4154 = (6077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4155) ≤ val WuPaper.ClassicalFourthData.Bq 4155
    have hp : val WuPaper.ClassicalFourthData.Bq 4155 = (234417729314056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4155 = 234417729314056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4155 = (2431:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4156) ≤ val WuPaper.ClassicalFourthData.Bq 4156
    have hp : val WuPaper.ClassicalFourthData.Bq 4156 = (234438792889872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4156 = 234438792889872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4156 = (3039:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4157) ≤ val WuPaper.ClassicalFourthData.Bq 4157
    have hp : val WuPaper.ClassicalFourthData.Bq 4157 = (234459848054143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4157 = 234459848054143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4157 = (12157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4158) ≤ val WuPaper.ClassicalFourthData.Bq 4158
    have hp : val WuPaper.ClassicalFourthData.Bq 4158 = (234480894810159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4158 = 234480894810159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4158 = (6079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4159) ≤ val WuPaper.ClassicalFourthData.Bq 4159
    have hp : val WuPaper.ClassicalFourthData.Bq 4159 = (234501933161205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4159 = 234501933161205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4159 = (12159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_259
