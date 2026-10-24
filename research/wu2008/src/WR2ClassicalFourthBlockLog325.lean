import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints325
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_325 (j : Fin 16) (hj : 16*325+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*325+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*325+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5200) ≤ val WuPaper.ClassicalFourthData.Bq 5200
    have hp : val WuPaper.ClassicalFourthData.Bq 5200 = (252396703919729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5200 = 252396703919729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5200 = (33:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5201) ≤ val WuPaper.ClassicalFourthData.Bq 5201
    have hp : val WuPaper.ClassicalFourthData.Bq 5201 = (252410518197208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5201 = 252410518197208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5201 = (13201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5202) ≤ val WuPaper.ClassicalFourthData.Bq 5202
    have hp : val WuPaper.ClassicalFourthData.Bq 5202 = (252424326803027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5202 = 252424326803027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5202 = (6601:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5203) ≤ val WuPaper.ClassicalFourthData.Bq 5203
    have hp : val WuPaper.ClassicalFourthData.Bq 5203 = (252438129739251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5203 = 252438129739251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5203 = (13203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5204) ≤ val WuPaper.ClassicalFourthData.Bq 5204
    have hp : val WuPaper.ClassicalFourthData.Bq 5204 = (252451927007947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5204 = 252451927007947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5204 = (3301:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5205) ≤ val WuPaper.ClassicalFourthData.Bq 5205
    have hp : val WuPaper.ClassicalFourthData.Bq 5205 = (252465718611179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5205 = 252465718611179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5205 = (2641:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5206) ≤ val WuPaper.ClassicalFourthData.Bq 5206
    have hp : val WuPaper.ClassicalFourthData.Bq 5206 = (252479504551011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5206 = 252479504551011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5206 = (6603:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5207) ≤ val WuPaper.ClassicalFourthData.Bq 5207
    have hp : val WuPaper.ClassicalFourthData.Bq 5207 = (252493284829506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5207 = 252493284829506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5207 = (13207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5207
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5208) ≤ val WuPaper.ClassicalFourthData.Bq 5208
    have hp : val WuPaper.ClassicalFourthData.Bq 5208 = (252507059448726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5208 = 252507059448726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5208 = (1651:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5209) ≤ val WuPaper.ClassicalFourthData.Bq 5209
    have hp : val WuPaper.ClassicalFourthData.Bq 5209 = (252520828410733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5209 = 252520828410733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5209 = (13209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5210) ≤ val WuPaper.ClassicalFourthData.Bq 5210
    have hp : val WuPaper.ClassicalFourthData.Bq 5210 = (252534591717586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5210 = 252534591717586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5210 = (1321:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5211) ≤ val WuPaper.ClassicalFourthData.Bq 5211
    have hp : val WuPaper.ClassicalFourthData.Bq 5211 = (252548349371345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5211 = 252548349371345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5211 = (13211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5212) ≤ val WuPaper.ClassicalFourthData.Bq 5212
    have hp : val WuPaper.ClassicalFourthData.Bq 5212 = (252562101374069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5212 = 252562101374069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5212 = (3303:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5213) ≤ val WuPaper.ClassicalFourthData.Bq 5213
    have hp : val WuPaper.ClassicalFourthData.Bq 5213 = (252575847727816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5213 = 252575847727816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5213 = (13213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5214) ≤ val WuPaper.ClassicalFourthData.Bq 5214
    have hp : val WuPaper.ClassicalFourthData.Bq 5214 = (252589588434641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5214 = 252589588434641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5214 = (6607:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5215) ≤ val WuPaper.ClassicalFourthData.Bq 5215
    have hp : val WuPaper.ClassicalFourthData.Bq 5215 = (252603323496602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5215 = 252603323496602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5215 = (2643:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_325
