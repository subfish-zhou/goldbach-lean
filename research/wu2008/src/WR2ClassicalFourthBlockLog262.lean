import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints262
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_262 (j : Fin 16) (hj : 16*262+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*262+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*262+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4192) ≤ val WuPaper.ClassicalFourthData.Bq 4192
    have hp : val WuPaper.ClassicalFourthData.Bq 4192 = (235191504979417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4192 = 235191504979417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4192 = (381:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4193) ≤ val WuPaper.ClassicalFourthData.Bq 4193
    have hp : val WuPaper.ClassicalFourthData.Bq 4193 = (235212259506205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4193 = 235212259506205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4193 = (12193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4194) ≤ val WuPaper.ClassicalFourthData.Bq 4194
    have hp : val WuPaper.ClassicalFourthData.Bq 4194 = (235233005742099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4194 = 235233005742099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4194 = (6097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4195) ≤ val WuPaper.ClassicalFourthData.Bq 4195
    have hp : val WuPaper.ClassicalFourthData.Bq 4195 = (235253743690333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4195 = 235253743690333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4195 = (2439:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4196) ≤ val WuPaper.ClassicalFourthData.Bq 4196
    have hp : val WuPaper.ClassicalFourthData.Bq 4196 = (235274473354137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4196 = 235274473354137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4196 = (3049:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4197) ≤ val WuPaper.ClassicalFourthData.Bq 4197
    have hp : val WuPaper.ClassicalFourthData.Bq 4197 = (235295194736740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4197 = 235295194736740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4197 = (12197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4198) ≤ val WuPaper.ClassicalFourthData.Bq 4198
    have hp : val WuPaper.ClassicalFourthData.Bq 4198 = (235315907841370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4198 = 235315907841370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4198 = (6099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4199) ≤ val WuPaper.ClassicalFourthData.Bq 4199
    have hp : val WuPaper.ClassicalFourthData.Bq 4199 = (235336612671252:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4199 = 235336612671252 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4199 = (12199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4200) ≤ val WuPaper.ClassicalFourthData.Bq 4200
    have hp : val WuPaper.ClassicalFourthData.Bq 4200 = (235357309229613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4200 = 235357309229613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4200 = (61:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4201) ≤ val WuPaper.ClassicalFourthData.Bq 4201
    have hp : val WuPaper.ClassicalFourthData.Bq 4201 = (235377997519674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4201 = 235377997519674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4201 = (12201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4202) ≤ val WuPaper.ClassicalFourthData.Bq 4202
    have hp : val WuPaper.ClassicalFourthData.Bq 4202 = (235398677544658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4202 = 235398677544658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4202 = (6101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4203) ≤ val WuPaper.ClassicalFourthData.Bq 4203
    have hp : val WuPaper.ClassicalFourthData.Bq 4203 = (235419349307785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4203 = 235419349307785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4203 = (12203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4204) ≤ val WuPaper.ClassicalFourthData.Bq 4204
    have hp : val WuPaper.ClassicalFourthData.Bq 4204 = (235440012812273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4204 = 235440012812273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4204 = (3051:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4205) ≤ val WuPaper.ClassicalFourthData.Bq 4205
    have hp : val WuPaper.ClassicalFourthData.Bq 4205 = (235460668061340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4205 = 235460668061340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4205 = (2441:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4206) ≤ val WuPaper.ClassicalFourthData.Bq 4206
    have hp : val WuPaper.ClassicalFourthData.Bq 4206 = (235481315058203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4206 = 235481315058203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4206 = (6103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4207) ≤ val WuPaper.ClassicalFourthData.Bq 4207
    have hp : val WuPaper.ClassicalFourthData.Bq 4207 = (235501953806074:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4207 = 235501953806074 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4207 = (12207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_262
