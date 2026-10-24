import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints448
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_448 (j : Fin 16) (hj : 16*448+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*448+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*448+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7168) ≤ val WuPaper.ClassicalFourthData.Bq 7168
    have hp : val WuPaper.ClassicalFourthData.Bq 7168 = (270769563528617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7168 = 270769563528617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7168 = (474:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7169) ≤ val WuPaper.ClassicalFourthData.Bq 7169
    have hp : val WuPaper.ClassicalFourthData.Bq 7169 = (270775324000050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7169 = 270775324000050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7169 = (15169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7170) ≤ val WuPaper.ClassicalFourthData.Bq 7170
    have hp : val WuPaper.ClassicalFourthData.Bq 7170 = (270781081598315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7170 = 270781081598315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7170 = (1517:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7171) ≤ val WuPaper.ClassicalFourthData.Bq 7171
    have hp : val WuPaper.ClassicalFourthData.Bq 7171 = (270786836324359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7171 = 270786836324359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7171 = (15171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7172) ≤ val WuPaper.ClassicalFourthData.Bq 7172
    have hp : val WuPaper.ClassicalFourthData.Bq 7172 = (270792588179128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7172 = 270792588179128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7172 = (3793:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7173) ≤ val WuPaper.ClassicalFourthData.Bq 7173
    have hp : val WuPaper.ClassicalFourthData.Bq 7173 = (270798337163568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7173 = 270798337163568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7173 = (15173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7174) ≤ val WuPaper.ClassicalFourthData.Bq 7174
    have hp : val WuPaper.ClassicalFourthData.Bq 7174 = (270804083278625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7174 = 270804083278625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7174 = (7587:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7175) ≤ val WuPaper.ClassicalFourthData.Bq 7175
    have hp : val WuPaper.ClassicalFourthData.Bq 7175 = (270809826525243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7175 = 270809826525243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7175 = (607:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7175
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7176) ≤ val WuPaper.ClassicalFourthData.Bq 7176
    have hp : val WuPaper.ClassicalFourthData.Bq 7176 = (270815566904367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7176 = 270815566904367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7176 = (1897:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7177) ≤ val WuPaper.ClassicalFourthData.Bq 7177
    have hp : val WuPaper.ClassicalFourthData.Bq 7177 = (270821304416942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7177 = 270821304416942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7177 = (15177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7178) ≤ val WuPaper.ClassicalFourthData.Bq 7178
    have hp : val WuPaper.ClassicalFourthData.Bq 7178 = (270827039063913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7178 = 270827039063913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7178 = (7589:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7179) ≤ val WuPaper.ClassicalFourthData.Bq 7179
    have hp : val WuPaper.ClassicalFourthData.Bq 7179 = (270832770846222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7179 = 270832770846222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7179 = (15179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7180) ≤ val WuPaper.ClassicalFourthData.Bq 7180
    have hp : val WuPaper.ClassicalFourthData.Bq 7180 = (270838499764813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7180 = 270838499764813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7180 = (759:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7181) ≤ val WuPaper.ClassicalFourthData.Bq 7181
    have hp : val WuPaper.ClassicalFourthData.Bq 7181 = (270844225820629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7181 = 270844225820629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7181 = (15181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7182) ≤ val WuPaper.ClassicalFourthData.Bq 7182
    have hp : val WuPaper.ClassicalFourthData.Bq 7182 = (270849949014614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7182 = 270849949014614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7182 = (7591:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7183) ≤ val WuPaper.ClassicalFourthData.Bq 7183
    have hp : val WuPaper.ClassicalFourthData.Bq 7183 = (270855669347709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7183 = 270855669347709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7183 = (15183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_448
