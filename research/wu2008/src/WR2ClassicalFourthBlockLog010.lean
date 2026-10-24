import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints010
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_010 (j : Fin 16) (hj : 16*10+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*10+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*10+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 160) ≤ val WuPaper.ClassicalFourthData.Bq 160
    have hp : val WuPaper.ClassicalFourthData.Bq 160 = (19225839781021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 160 = 19225839781021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 160 = (51:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 161) ≤ val WuPaper.ClassicalFourthData.Bq 161
    have hp : val WuPaper.ClassicalFourthData.Bq 161 = (19341290959890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 161 = 19341290959890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 161 = (8161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 162) ≤ val WuPaper.ClassicalFourthData.Bq 162
    have hp : val WuPaper.ClassicalFourthData.Bq 162 = (19456685543520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 162 = 19456685543520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 162 = (4081:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 163) ≤ val WuPaper.ClassicalFourthData.Bq 163
    have hp : val WuPaper.ClassicalFourthData.Bq 163 = (19572023566311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 163 = 19572023566311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 163 = (8163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 164) ≤ val WuPaper.ClassicalFourthData.Bq 164
    have hp : val WuPaper.ClassicalFourthData.Bq 164 = (19687305062632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 164 = 19687305062632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 164 = (2041:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 165) ≤ val WuPaper.ClassicalFourthData.Bq 165
    have hp : val WuPaper.ClassicalFourthData.Bq 165 = (19802530066830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 165 = 19802530066830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 165 = (1633:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 166) ≤ val WuPaper.ClassicalFourthData.Bq 166
    have hp : val WuPaper.ClassicalFourthData.Bq 166 = (19917698613221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 166 = 19917698613221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 166 = (4083:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 167) ≤ val WuPaper.ClassicalFourthData.Bq 167
    have hp : val WuPaper.ClassicalFourthData.Bq 167 = (20032810736097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 167 = 20032810736097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 167 = (8167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_167
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 168) ≤ val WuPaper.ClassicalFourthData.Bq 168
    have hp : val WuPaper.ClassicalFourthData.Bq 168 = (20147866469724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 168 = 20147866469724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 168 = (1021:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 169) ≤ val WuPaper.ClassicalFourthData.Bq 169
    have hp : val WuPaper.ClassicalFourthData.Bq 169 = (20262865848339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 169 = 20262865848339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 169 = (8169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 170) ≤ val WuPaper.ClassicalFourthData.Bq 170
    have hp : val WuPaper.ClassicalFourthData.Bq 170 = (20377808906154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 170 = 20377808906154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 170 = (817:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 171) ≤ val WuPaper.ClassicalFourthData.Bq 171
    have hp : val WuPaper.ClassicalFourthData.Bq 171 = (20492695677356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 171 = 20492695677356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 171 = (8171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 172) ≤ val WuPaper.ClassicalFourthData.Bq 172
    have hp : val WuPaper.ClassicalFourthData.Bq 172 = (20607526196102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 172 = 20607526196102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 172 = (2043:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 173) ≤ val WuPaper.ClassicalFourthData.Bq 173
    have hp : val WuPaper.ClassicalFourthData.Bq 173 = (20722300496526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 173 = 20722300496526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 173 = (8173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 174) ≤ val WuPaper.ClassicalFourthData.Bq 174
    have hp : val WuPaper.ClassicalFourthData.Bq 174 = (20837018612733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 174 = 20837018612733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 174 = (4087:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 175) ≤ val WuPaper.ClassicalFourthData.Bq 175
    have hp : val WuPaper.ClassicalFourthData.Bq 175 = (20951680578803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 175 = 20951680578803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 175 = (327:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_175
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_010
