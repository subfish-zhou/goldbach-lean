import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints324
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_324 (j : Fin 16) (hj : 16*324+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*324+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*324+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5184) ≤ val WuPaper.ClassicalFourthData.Bq 5184
    have hp : val WuPaper.ClassicalFourthData.Bq 5184 = (252174902444576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5184 = 252174902444576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5184 = (412:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5185) ≤ val WuPaper.ClassicalFourthData.Bq 5185
    have hp : val WuPaper.ClassicalFourthData.Bq 5185 = (252188807750383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5185 = 252188807750383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5185 = (2637:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5186) ≤ val WuPaper.ClassicalFourthData.Bq 5186
    have hp : val WuPaper.ClassicalFourthData.Bq 5186 = (252202707351347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5186 = 252202707351347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5186 = (6593:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5187) ≤ val WuPaper.ClassicalFourthData.Bq 5187
    have hp : val WuPaper.ClassicalFourthData.Bq 5187 = (252216601249546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5187 = 252216601249546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5187 = (13187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5188) ≤ val WuPaper.ClassicalFourthData.Bq 5188
    have hp : val WuPaper.ClassicalFourthData.Bq 5188 = (252230489447062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5188 = 252230489447062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5188 = (3297:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5189) ≤ val WuPaper.ClassicalFourthData.Bq 5189
    have hp : val WuPaper.ClassicalFourthData.Bq 5189 = (252244371945973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5189 = 252244371945973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5189 = (13189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5190) ≤ val WuPaper.ClassicalFourthData.Bq 5190
    have hp : val WuPaper.ClassicalFourthData.Bq 5190 = (252258248748357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5190 = 252258248748357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5190 = (1319:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5191) ≤ val WuPaper.ClassicalFourthData.Bq 5191
    have hp : val WuPaper.ClassicalFourthData.Bq 5191 = (252272119856291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5191 = 252272119856291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5191 = (13191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5191
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5192) ≤ val WuPaper.ClassicalFourthData.Bq 5192
    have hp : val WuPaper.ClassicalFourthData.Bq 5192 = (252285985271852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5192 = 252285985271852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5192 = (1649:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5193) ≤ val WuPaper.ClassicalFourthData.Bq 5193
    have hp : val WuPaper.ClassicalFourthData.Bq 5193 = (252299844997114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5193 = 252299844997114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5193 = (13193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5194) ≤ val WuPaper.ClassicalFourthData.Bq 5194
    have hp : val WuPaper.ClassicalFourthData.Bq 5194 = (252313699034151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5194 = 252313699034151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5194 = (6597:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5195) ≤ val WuPaper.ClassicalFourthData.Bq 5195
    have hp : val WuPaper.ClassicalFourthData.Bq 5195 = (252327547385039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5195 = 252327547385039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5195 = (2639:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5196) ≤ val WuPaper.ClassicalFourthData.Bq 5196
    have hp : val WuPaper.ClassicalFourthData.Bq 5196 = (252341390051848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5196 = 252341390051848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5196 = (3299:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5197) ≤ val WuPaper.ClassicalFourthData.Bq 5197
    have hp : val WuPaper.ClassicalFourthData.Bq 5197 = (252355227036652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5197 = 252355227036652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5197 = (13197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5198) ≤ val WuPaper.ClassicalFourthData.Bq 5198
    have hp : val WuPaper.ClassicalFourthData.Bq 5198 = (252369058341520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5198 = 252369058341520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5198 = (6599:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5199) ≤ val WuPaper.ClassicalFourthData.Bq 5199
    have hp : val WuPaper.ClassicalFourthData.Bq 5199 = (252382883968523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5199 = 252382883968523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5199 = (13199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5199
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_324
