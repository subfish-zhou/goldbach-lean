import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints387
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_387 (j : Fin 16) (hj : 16*387+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*387+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*387+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6192) ≤ val WuPaper.ClassicalFourthData.Bq 6192
    have hp : val WuPaper.ClassicalFourthData.Bq 6192 = (263615765983638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6192 = 263615765983638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6192 = (887:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6193) ≤ val WuPaper.ClassicalFourthData.Bq 6193
    have hp : val WuPaper.ClassicalFourthData.Bq 6193 = (263624842969468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6193 = 263624842969468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6193 = (14193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6194) ≤ val WuPaper.ClassicalFourthData.Bq 6194
    have hp : val WuPaper.ClassicalFourthData.Bq 6194 = (263633915963926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6194 = 263633915963926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6194 = (7097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6195) ≤ val WuPaper.ClassicalFourthData.Bq 6195
    have hp : val WuPaper.ClassicalFourthData.Bq 6195 = (263642984968386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6195 = 263642984968386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6195 = (2839:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6196) ≤ val WuPaper.ClassicalFourthData.Bq 6196
    have hp : val WuPaper.ClassicalFourthData.Bq 6196 = (263652049984224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6196 = 263652049984224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6196 = (3549:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6197) ≤ val WuPaper.ClassicalFourthData.Bq 6197
    have hp : val WuPaper.ClassicalFourthData.Bq 6197 = (263661111012814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6197 = 263661111012814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6197 = (14197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6198) ≤ val WuPaper.ClassicalFourthData.Bq 6198
    have hp : val WuPaper.ClassicalFourthData.Bq 6198 = (263670168055530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6198 = 263670168055530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6198 = (7099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6199) ≤ val WuPaper.ClassicalFourthData.Bq 6199
    have hp : val WuPaper.ClassicalFourthData.Bq 6199 = (263679221113747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6199 = 263679221113747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6199 = (14199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6200) ≤ val WuPaper.ClassicalFourthData.Bq 6200
    have hp : val WuPaper.ClassicalFourthData.Bq 6200 = (263688270188836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6200 = 263688270188836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6200 = (71:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6201) ≤ val WuPaper.ClassicalFourthData.Bq 6201
    have hp : val WuPaper.ClassicalFourthData.Bq 6201 = (263697315282170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6201 = 263697315282170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6201 = (14201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6202) ≤ val WuPaper.ClassicalFourthData.Bq 6202
    have hp : val WuPaper.ClassicalFourthData.Bq 6202 = (263706356395121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6202 = 263706356395121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6202 = (7101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6203) ≤ val WuPaper.ClassicalFourthData.Bq 6203
    have hp : val WuPaper.ClassicalFourthData.Bq 6203 = (263715393529060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6203 = 263715393529060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6203 = (14203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6204) ≤ val WuPaper.ClassicalFourthData.Bq 6204
    have hp : val WuPaper.ClassicalFourthData.Bq 6204 = (263724426685358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6204 = 263724426685358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6204 = (3551:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6205) ≤ val WuPaper.ClassicalFourthData.Bq 6205
    have hp : val WuPaper.ClassicalFourthData.Bq 6205 = (263733455865385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6205 = 263733455865385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6205 = (2841:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6206) ≤ val WuPaper.ClassicalFourthData.Bq 6206
    have hp : val WuPaper.ClassicalFourthData.Bq 6206 = (263742481070511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6206 = 263742481070511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6206 = (7103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6207) ≤ val WuPaper.ClassicalFourthData.Bq 6207
    have hp : val WuPaper.ClassicalFourthData.Bq 6207 = (263751502302105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6207 = 263751502302105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6207 = (14207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_387
