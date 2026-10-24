import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints572
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_572 (j : Fin 16) (hj : 16*572+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*572+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*572+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9152) ≤ val WuPaper.ClassicalFourthData.Bq 9152
    have hp : val WuPaper.ClassicalFourthData.Bq 9152 = (277583833306276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9152 = 277583833306276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9152 = (536:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9153) ≤ val WuPaper.ClassicalFourthData.Bq 9153
    have hp : val WuPaper.ClassicalFourthData.Bq 9153 = (277585380607514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9153 = 277585380607514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9153 = (17153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9154) ≤ val WuPaper.ClassicalFourthData.Bq 9154
    have hp : val WuPaper.ClassicalFourthData.Bq 9154 = (277586926380489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9154 = 277586926380489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9154 = (8577:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9155) ≤ val WuPaper.ClassicalFourthData.Bq 9155
    have hp : val WuPaper.ClassicalFourthData.Bq 9155 = (277588470625676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9155 = 277588470625676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9155 = (3431:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9156) ≤ val WuPaper.ClassicalFourthData.Bq 9156
    have hp : val WuPaper.ClassicalFourthData.Bq 9156 = (277590013343545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9156 = 277590013343545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9156 = (4289:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9157) ≤ val WuPaper.ClassicalFourthData.Bq 9157
    have hp : val WuPaper.ClassicalFourthData.Bq 9157 = (277591554534568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9157 = 277591554534568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9157 = (17157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9158) ≤ val WuPaper.ClassicalFourthData.Bq 9158
    have hp : val WuPaper.ClassicalFourthData.Bq 9158 = (277593094199217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9158 = 277593094199217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9158 = (8579:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9159) ≤ val WuPaper.ClassicalFourthData.Bq 9159
    have hp : val WuPaper.ClassicalFourthData.Bq 9159 = (277594632337964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9159 = 277594632337964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9159 = (17159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9159
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9160) ≤ val WuPaper.ClassicalFourthData.Bq 9160
    have hp : val WuPaper.ClassicalFourthData.Bq 9160 = (277596168951280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9160 = 277596168951280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9160 = (429:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9161) ≤ val WuPaper.ClassicalFourthData.Bq 9161
    have hp : val WuPaper.ClassicalFourthData.Bq 9161 = (277597704039636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9161 = 277597704039636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9161 = (17161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9162) ≤ val WuPaper.ClassicalFourthData.Bq 9162
    have hp : val WuPaper.ClassicalFourthData.Bq 9162 = (277599237603503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9162 = 277599237603503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9162 = (8581:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9163) ≤ val WuPaper.ClassicalFourthData.Bq 9163
    have hp : val WuPaper.ClassicalFourthData.Bq 9163 = (277600769643352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9163 = 277600769643352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9163 = (17163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9164) ≤ val WuPaper.ClassicalFourthData.Bq 9164
    have hp : val WuPaper.ClassicalFourthData.Bq 9164 = (277602300159655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9164 = 277602300159655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9164 = (4291:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9165) ≤ val WuPaper.ClassicalFourthData.Bq 9165
    have hp : val WuPaper.ClassicalFourthData.Bq 9165 = (277603829152881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9165 = 277603829152881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9165 = (3433:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9166) ≤ val WuPaper.ClassicalFourthData.Bq 9166
    have hp : val WuPaper.ClassicalFourthData.Bq 9166 = (277605356623501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9166 = 277605356623501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9166 = (8583:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9167) ≤ val WuPaper.ClassicalFourthData.Bq 9167
    have hp : val WuPaper.ClassicalFourthData.Bq 9167 = (277606882571985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9167 = 277606882571985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9167 = (17167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_572
