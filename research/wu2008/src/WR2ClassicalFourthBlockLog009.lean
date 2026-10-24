import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints009
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_009 (j : Fin 16) (hj : 16*9+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*9+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*9+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 144) ≤ val WuPaper.ClassicalFourthData.Bq 144
    have hp : val WuPaper.ClassicalFourthData.Bq 144 = (17370895794348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 144 = 17370895794348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 144 = (509:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 145) ≤ val WuPaper.ClassicalFourthData.Bq 145
    have hp : val WuPaper.ClassicalFourthData.Bq 145 = (17487257196989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 145 = 17487257196989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 145 = (1629:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 146) ≤ val WuPaper.ClassicalFourthData.Bq 146
    have hp : val WuPaper.ClassicalFourthData.Bq 146 = (17603561450380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 146 = 17603561450380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 146 = (4073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 147) ≤ val WuPaper.ClassicalFourthData.Bq 147
    have hp : val WuPaper.ClassicalFourthData.Bq 147 = (17719808589348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 147 = 17719808589348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 147 = (8147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 148) ≤ val WuPaper.ClassicalFourthData.Bq 148
    have hp : val WuPaper.ClassicalFourthData.Bq 148 = (17835998648695:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 148 = 17835998648695 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 148 = (2037:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 149) ≤ val WuPaper.ClassicalFourthData.Bq 149
    have hp : val WuPaper.ClassicalFourthData.Bq 149 = (17952131663194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 149 = 17952131663194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 149 = (8149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 150) ≤ val WuPaper.ClassicalFourthData.Bq 150
    have hp : val WuPaper.ClassicalFourthData.Bq 150 = (18068207667591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 150 = 18068207667591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 150 = (163:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 151) ≤ val WuPaper.ClassicalFourthData.Bq 151
    have hp : val WuPaper.ClassicalFourthData.Bq 151 = (18184226696608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 151 = 18184226696608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 151 = (8151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 152) ≤ val WuPaper.ClassicalFourthData.Bq 152
    have hp : val WuPaper.ClassicalFourthData.Bq 152 = (18300188784935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 152 = 18300188784935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 152 = (1019:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 153) ≤ val WuPaper.ClassicalFourthData.Bq 153
    have hp : val WuPaper.ClassicalFourthData.Bq 153 = (18416093967240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 153 = 18416093967240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 153 = (8153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 154) ≤ val WuPaper.ClassicalFourthData.Bq 154
    have hp : val WuPaper.ClassicalFourthData.Bq 154 = (18531942278161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 154 = 18531942278161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 154 = (4077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 155) ≤ val WuPaper.ClassicalFourthData.Bq 155
    have hp : val WuPaper.ClassicalFourthData.Bq 155 = (18647733752310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 155 = 18647733752310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 155 = (1631:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 156) ≤ val WuPaper.ClassicalFourthData.Bq 156
    have hp : val WuPaper.ClassicalFourthData.Bq 156 = (18763468424272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 156 = 18763468424272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 156 = (2039:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 157) ≤ val WuPaper.ClassicalFourthData.Bq 157
    have hp : val WuPaper.ClassicalFourthData.Bq 157 = (18879146328606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 157 = 18879146328606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 157 = (8157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 158) ≤ val WuPaper.ClassicalFourthData.Bq 158
    have hp : val WuPaper.ClassicalFourthData.Bq 158 = (18994767499844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 158 = 18994767499844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 158 = (4079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 159) ≤ val WuPaper.ClassicalFourthData.Bq 159
    have hp : val WuPaper.ClassicalFourthData.Bq 159 = (19110331972489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 159 = 19110331972489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 159 = (8159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_009
