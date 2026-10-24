import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints011
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_011 (j : Fin 16) (hj : 16*11+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*11+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*11+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 176) ≤ val WuPaper.ClassicalFourthData.Bq 176
    have hp : val WuPaper.ClassicalFourthData.Bq 176 = (21066286428791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 176 = 21066286428791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 176 = (511:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 177) ≤ val WuPaper.ClassicalFourthData.Bq 177
    have hp : val WuPaper.ClassicalFourthData.Bq 177 = (21180836196722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 177 = 21180836196722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 177 = (8177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 178) ≤ val WuPaper.ClassicalFourthData.Bq 178
    have hp : val WuPaper.ClassicalFourthData.Bq 178 = (21295329916598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 178 = 21295329916598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 178 = (4089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 179) ≤ val WuPaper.ClassicalFourthData.Bq 179
    have hp : val WuPaper.ClassicalFourthData.Bq 179 = (21409767622393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 179 = 21409767622393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 179 = (8179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 180) ≤ val WuPaper.ClassicalFourthData.Bq 180
    have hp : val WuPaper.ClassicalFourthData.Bq 180 = (21524149348056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 180 = 21524149348056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 180 = (409:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 181) ≤ val WuPaper.ClassicalFourthData.Bq 181
    have hp : val WuPaper.ClassicalFourthData.Bq 181 = (21638475127509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 181 = 21638475127509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 181 = (8181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 182) ≤ val WuPaper.ClassicalFourthData.Bq 182
    have hp : val WuPaper.ClassicalFourthData.Bq 182 = (21752744994648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 182 = 21752744994648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 182 = (4091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 183) ≤ val WuPaper.ClassicalFourthData.Bq 183
    have hp : val WuPaper.ClassicalFourthData.Bq 183 = (21866958983342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 183 = 21866958983342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 183 = (8183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 184) ≤ val WuPaper.ClassicalFourthData.Bq 184
    have hp : val WuPaper.ClassicalFourthData.Bq 184 = (21981117127435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 184 = 21981117127435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 184 = (1023:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 185) ≤ val WuPaper.ClassicalFourthData.Bq 185
    have hp : val WuPaper.ClassicalFourthData.Bq 185 = (22095219460745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 185 = 22095219460745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 185 = (1637:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 186) ≤ val WuPaper.ClassicalFourthData.Bq 186
    have hp : val WuPaper.ClassicalFourthData.Bq 186 = (22209266017062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 186 = 22209266017062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 186 = (4093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 187) ≤ val WuPaper.ClassicalFourthData.Bq 187
    have hp : val WuPaper.ClassicalFourthData.Bq 187 = (22323256830154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 187 = 22323256830154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 187 = (8187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 188) ≤ val WuPaper.ClassicalFourthData.Bq 188
    have hp : val WuPaper.ClassicalFourthData.Bq 188 = (22437191933757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 188 = 22437191933757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 188 = (2047:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 189) ≤ val WuPaper.ClassicalFourthData.Bq 189
    have hp : val WuPaper.ClassicalFourthData.Bq 189 = (22551071361587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 189 = 22551071361587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 189 = (8189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 190) ≤ val WuPaper.ClassicalFourthData.Bq 190
    have hp : val WuPaper.ClassicalFourthData.Bq 190 = (22664895147329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 190 = 22664895147329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 190 = (819:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 191) ≤ val WuPaper.ClassicalFourthData.Bq 191
    have hp : val WuPaper.ClassicalFourthData.Bq 191 = (22778663324646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 191 = 22778663324646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 191 = (8191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_011
