import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints015
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_015 (j : Fin 16) (hj : 16*15+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*15+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*15+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 240) ≤ val WuPaper.ClassicalFourthData.Bq 240
    have hp : val WuPaper.ClassicalFourthData.Bq 240 = (28285877730086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 240 = 28285877730086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 240 = (103:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 241) ≤ val WuPaper.ClassicalFourthData.Bq 241
    have hp : val WuPaper.ClassicalFourthData.Bq 241 = (28396907837672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 241 = 28396907837672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 241 = (8241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 242) ≤ val WuPaper.ClassicalFourthData.Bq 242
    have hp : val WuPaper.ClassicalFourthData.Bq 242 = (28507884019704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 242 = 28507884019704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 242 = (4121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 243) ≤ val WuPaper.ClassicalFourthData.Bq 243
    have hp : val WuPaper.ClassicalFourthData.Bq 243 = (28618806308528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 243 = 28618806308528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 243 = (8243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 244) ≤ val WuPaper.ClassicalFourthData.Bq 244
    have hp : val WuPaper.ClassicalFourthData.Bq 244 = (28729674736461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 244 = 28729674736461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 244 = (2061:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 245) ≤ val WuPaper.ClassicalFourthData.Bq 245
    have hp : val WuPaper.ClassicalFourthData.Bq 245 = (28840489335802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 245 = 28840489335802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 245 = (1649:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 246) ≤ val WuPaper.ClassicalFourthData.Bq 246
    have hp : val WuPaper.ClassicalFourthData.Bq 246 = (28951250138819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 246 = 28951250138819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 246 = (4123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 247) ≤ val WuPaper.ClassicalFourthData.Bq 247
    have hp : val WuPaper.ClassicalFourthData.Bq 247 = (29061957177759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 247 = 29061957177759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 247 = (8247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 248) ≤ val WuPaper.ClassicalFourthData.Bq 248
    have hp : val WuPaper.ClassicalFourthData.Bq 248 = (29172610484844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 248 = 29172610484844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 248 = (1031:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 249) ≤ val WuPaper.ClassicalFourthData.Bq 249
    have hp : val WuPaper.ClassicalFourthData.Bq 249 = (29283210092271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 249 = 29283210092271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 249 = (8249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 250) ≤ val WuPaper.ClassicalFourthData.Bq 250
    have hp : val WuPaper.ClassicalFourthData.Bq 250 = (29393756032211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 250 = 29393756032211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 250 = (33:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 251) ≤ val WuPaper.ClassicalFourthData.Bq 251
    have hp : val WuPaper.ClassicalFourthData.Bq 251 = (29504248336814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 251 = 29504248336814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 251 = (8251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 252) ≤ val WuPaper.ClassicalFourthData.Bq 252
    have hp : val WuPaper.ClassicalFourthData.Bq 252 = (29614687038203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 252 = 29614687038203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 252 = (2063:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 253) ≤ val WuPaper.ClassicalFourthData.Bq 253
    have hp : val WuPaper.ClassicalFourthData.Bq 253 = (29725072168475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 253 = 29725072168475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 253 = (8253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 254) ≤ val WuPaper.ClassicalFourthData.Bq 254
    have hp : val WuPaper.ClassicalFourthData.Bq 254 = (29835403759707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 254 = 29835403759707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 254 = (4127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 255) ≤ val WuPaper.ClassicalFourthData.Bq 255
    have hp : val WuPaper.ClassicalFourthData.Bq 255 = (29945681843948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 255 = 29945681843948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 255 = (1651:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_015
