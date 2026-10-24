import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints635
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_635 (j : Fin 16) (hj : 16*635+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*635+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*635+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10160) ≤ val WuPaper.ClassicalFourthData.Bq 10160
    have hp : val WuPaper.ClassicalFourthData.Bq 10160 = (278442010411359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10160 = 278442010411359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10160 = (227:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10161) ≤ val WuPaper.ClassicalFourthData.Bq 10161
    have hp : val WuPaper.ClassicalFourthData.Bq 10161 = (278442232529729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10161 = 278442232529729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10161 = (18161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10162) ≤ val WuPaper.ClassicalFourthData.Bq 10162
    have hp : val WuPaper.ClassicalFourthData.Bq 10162 = (278442453525372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10162 = 278442453525372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10162 = (9081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10163) ≤ val WuPaper.ClassicalFourthData.Bq 10163
    have hp : val WuPaper.ClassicalFourthData.Bq 10163 = (278442673398626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10163 = 278442673398626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10163 = (18163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10164) ≤ val WuPaper.ClassicalFourthData.Bq 10164
    have hp : val WuPaper.ClassicalFourthData.Bq 10164 = (278442892149834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10164 = 278442892149834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10164 = (4541:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10165) ≤ val WuPaper.ClassicalFourthData.Bq 10165
    have hp : val WuPaper.ClassicalFourthData.Bq 10165 = (278443109779336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10165 = 278443109779336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10165 = (3633:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10166) ≤ val WuPaper.ClassicalFourthData.Bq 10166
    have hp : val WuPaper.ClassicalFourthData.Bq 10166 = (278443326287470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10166 = 278443326287470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10166 = (9083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10167) ≤ val WuPaper.ClassicalFourthData.Bq 10167
    have hp : val WuPaper.ClassicalFourthData.Bq 10167 = (278443541674579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10167 = 278443541674579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10167 = (18167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10168) ≤ val WuPaper.ClassicalFourthData.Bq 10168
    have hp : val WuPaper.ClassicalFourthData.Bq 10168 = (278443755941000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10168 = 278443755941000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10168 = (2271:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10169) ≤ val WuPaper.ClassicalFourthData.Bq 10169
    have hp : val WuPaper.ClassicalFourthData.Bq 10169 = (278443969087076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10169 = 278443969087076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10169 = (18169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10170) ≤ val WuPaper.ClassicalFourthData.Bq 10170
    have hp : val WuPaper.ClassicalFourthData.Bq 10170 = (278444181113144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10170 = 278444181113144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10170 = (1817:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10171) ≤ val WuPaper.ClassicalFourthData.Bq 10171
    have hp : val WuPaper.ClassicalFourthData.Bq 10171 = (278444392019545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10171 = 278444392019545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10171 = (18171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10172) ≤ val WuPaper.ClassicalFourthData.Bq 10172
    have hp : val WuPaper.ClassicalFourthData.Bq 10172 = (278444601806619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10172 = 278444601806619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10172 = (4543:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10173) ≤ val WuPaper.ClassicalFourthData.Bq 10173
    have hp : val WuPaper.ClassicalFourthData.Bq 10173 = (278444810474705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10173 = 278444810474705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10173 = (18173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10174) ≤ val WuPaper.ClassicalFourthData.Bq 10174
    have hp : val WuPaper.ClassicalFourthData.Bq 10174 = (278445018024142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10174 = 278445018024142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10174 = (9087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10175) ≤ val WuPaper.ClassicalFourthData.Bq 10175
    have hp : val WuPaper.ClassicalFourthData.Bq 10175 = (278445224455269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10175 = 278445224455269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10175 = (727:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_635
