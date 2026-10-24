import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints385
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_385 (j : Fin 16) (hj : 16*385+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*385+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*385+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6160) ≤ val WuPaper.ClassicalFourthData.Bq 6160
    have hp : val WuPaper.ClassicalFourthData.Bq 6160 = (263323186731772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6160 = 263323186731772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6160 = (177:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6161) ≤ val WuPaper.ClassicalFourthData.Bq 6161
    have hp : val WuPaper.ClassicalFourthData.Bq 6161 = (263332392171141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6161 = 263332392171141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6161 = (14161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6162) ≤ val WuPaper.ClassicalFourthData.Bq 6162
    have hp : val WuPaper.ClassicalFourthData.Bq 6162 = (263341593574828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6162 = 263341593574828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6162 = (7081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6163) ≤ val WuPaper.ClassicalFourthData.Bq 6163
    have hp : val WuPaper.ClassicalFourthData.Bq 6163 = (263350790944226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6163 = 263350790944226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6163 = (14163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6164) ≤ val WuPaper.ClassicalFourthData.Bq 6164
    have hp : val WuPaper.ClassicalFourthData.Bq 6164 = (263359984280727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6164 = 263359984280727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6164 = (3541:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6165) ≤ val WuPaper.ClassicalFourthData.Bq 6165
    have hp : val WuPaper.ClassicalFourthData.Bq 6165 = (263369173585725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6165 = 263369173585725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6165 = (2833:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6166) ≤ val WuPaper.ClassicalFourthData.Bq 6166
    have hp : val WuPaper.ClassicalFourthData.Bq 6166 = (263378358860610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6166 = 263378358860610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6166 = (7083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6167) ≤ val WuPaper.ClassicalFourthData.Bq 6167
    have hp : val WuPaper.ClassicalFourthData.Bq 6167 = (263387540106773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6167 = 263387540106773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6167 = (14167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6168) ≤ val WuPaper.ClassicalFourthData.Bq 6168
    have hp : val WuPaper.ClassicalFourthData.Bq 6168 = (263396717325604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6168 = 263396717325604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6168 = (1771:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6169) ≤ val WuPaper.ClassicalFourthData.Bq 6169
    have hp : val WuPaper.ClassicalFourthData.Bq 6169 = (263405890518495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6169 = 263405890518495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6169 = (14169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6170) ≤ val WuPaper.ClassicalFourthData.Bq 6170
    have hp : val WuPaper.ClassicalFourthData.Bq 6170 = (263415059686833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6170 = 263415059686833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6170 = (1417:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6171) ≤ val WuPaper.ClassicalFourthData.Bq 6171
    have hp : val WuPaper.ClassicalFourthData.Bq 6171 = (263424224832008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6171 = 263424224832008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6171 = (14171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6172) ≤ val WuPaper.ClassicalFourthData.Bq 6172
    have hp : val WuPaper.ClassicalFourthData.Bq 6172 = (263433385955408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6172 = 263433385955408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6172 = (3543:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6173) ≤ val WuPaper.ClassicalFourthData.Bq 6173
    have hp : val WuPaper.ClassicalFourthData.Bq 6173 = (263442543058421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6173 = 263442543058421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6173 = (14173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6174) ≤ val WuPaper.ClassicalFourthData.Bq 6174
    have hp : val WuPaper.ClassicalFourthData.Bq 6174 = (263451696142433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6174 = 263451696142433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6174 = (7087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6175) ≤ val WuPaper.ClassicalFourthData.Bq 6175
    have hp : val WuPaper.ClassicalFourthData.Bq 6175 = (263460845208832:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6175 = 263460845208832 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6175 = (567:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_385
