import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints386
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_386 (j : Fin 16) (hj : 16*386+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*386+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*386+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6176) ≤ val WuPaper.ClassicalFourthData.Bq 6176
    have hp : val WuPaper.ClassicalFourthData.Bq 6176 = (263469990259003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6176 = 263469990259003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6176 = (443:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6177) ≤ val WuPaper.ClassicalFourthData.Bq 6177
    have hp : val WuPaper.ClassicalFourthData.Bq 6177 = (263479131294331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6177 = 263479131294331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6177 = (14177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6178) ≤ val WuPaper.ClassicalFourthData.Bq 6178
    have hp : val WuPaper.ClassicalFourthData.Bq 6178 = (263488268316202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6178 = 263488268316202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6178 = (7089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6179) ≤ val WuPaper.ClassicalFourthData.Bq 6179
    have hp : val WuPaper.ClassicalFourthData.Bq 6179 = (263497401326001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6179 = 263497401326001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6179 = (14179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6180) ≤ val WuPaper.ClassicalFourthData.Bq 6180
    have hp : val WuPaper.ClassicalFourthData.Bq 6180 = (263506530325110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6180 = 263506530325110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6180 = (709:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6181) ≤ val WuPaper.ClassicalFourthData.Bq 6181
    have hp : val WuPaper.ClassicalFourthData.Bq 6181 = (263515655314914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6181 = 263515655314914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6181 = (14181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6182) ≤ val WuPaper.ClassicalFourthData.Bq 6182
    have hp : val WuPaper.ClassicalFourthData.Bq 6182 = (263524776296794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6182 = 263524776296794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6182 = (7091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6183) ≤ val WuPaper.ClassicalFourthData.Bq 6183
    have hp : val WuPaper.ClassicalFourthData.Bq 6183 = (263533893272134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6183 = 263533893272134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6183 = (14183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6184) ≤ val WuPaper.ClassicalFourthData.Bq 6184
    have hp : val WuPaper.ClassicalFourthData.Bq 6184 = (263543006242314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6184 = 263543006242314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6184 = (1773:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6185) ≤ val WuPaper.ClassicalFourthData.Bq 6185
    have hp : val WuPaper.ClassicalFourthData.Bq 6185 = (263552115208716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6185 = 263552115208716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6185 = (2837:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6186) ≤ val WuPaper.ClassicalFourthData.Bq 6186
    have hp : val WuPaper.ClassicalFourthData.Bq 6186 = (263561220172720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6186 = 263561220172720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6186 = (7093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6187) ≤ val WuPaper.ClassicalFourthData.Bq 6187
    have hp : val WuPaper.ClassicalFourthData.Bq 6187 = (263570321135707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6187 = 263570321135707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6187 = (14187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6188) ≤ val WuPaper.ClassicalFourthData.Bq 6188
    have hp : val WuPaper.ClassicalFourthData.Bq 6188 = (263579418099056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6188 = 263579418099056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6188 = (3547:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6189) ≤ val WuPaper.ClassicalFourthData.Bq 6189
    have hp : val WuPaper.ClassicalFourthData.Bq 6189 = (263588511064145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6189 = 263588511064145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6189 = (14189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6190) ≤ val WuPaper.ClassicalFourthData.Bq 6190
    have hp : val WuPaper.ClassicalFourthData.Bq 6190 = (263597600032353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6190 = 263597600032353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6190 = (1419:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6191) ≤ val WuPaper.ClassicalFourthData.Bq 6191
    have hp : val WuPaper.ClassicalFourthData.Bq 6191 = (263606685005059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6191 = 263606685005059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6191 = (14191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_386
