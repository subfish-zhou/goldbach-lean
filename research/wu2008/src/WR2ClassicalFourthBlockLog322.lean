import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints322
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_322 (j : Fin 16) (hj : 16*322+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*322+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*322+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5152) ≤ val WuPaper.ClassicalFourthData.Bq 5152
    have hp : val WuPaper.ClassicalFourthData.Bq 5152 = (251726908004122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5152 = 251726908004122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5152 = (411:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5153) ≤ val WuPaper.ClassicalFourthData.Bq 5153
    have hp : val WuPaper.ClassicalFourthData.Bq 5153 = (251740996968830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5153 = 251740996968830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5153 = (13153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5154) ≤ val WuPaper.ClassicalFourthData.Bq 5154
    have hp : val WuPaper.ClassicalFourthData.Bq 5154 = (251755080161643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5154 = 251755080161643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5154 = (6577:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5155) ≤ val WuPaper.ClassicalFourthData.Bq 5155
    have hp : val WuPaper.ClassicalFourthData.Bq 5155 = (251769157584671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5155 = 251769157584671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5155 = (2631:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5156) ≤ val WuPaper.ClassicalFourthData.Bq 5156
    have hp : val WuPaper.ClassicalFourthData.Bq 5156 = (251783229240022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5156 = 251783229240022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5156 = (3289:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5157) ≤ val WuPaper.ClassicalFourthData.Bq 5157
    have hp : val WuPaper.ClassicalFourthData.Bq 5157 = (251797295129804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5157 = 251797295129804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5157 = (13157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5158) ≤ val WuPaper.ClassicalFourthData.Bq 5158
    have hp : val WuPaper.ClassicalFourthData.Bq 5158 = (251811355256123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5158 = 251811355256123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5158 = (6579:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5159) ≤ val WuPaper.ClassicalFourthData.Bq 5159
    have hp : val WuPaper.ClassicalFourthData.Bq 5159 = (251825409621084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5159 = 251825409621084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5159 = (13159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5159
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5160) ≤ val WuPaper.ClassicalFourthData.Bq 5160
    have hp : val WuPaper.ClassicalFourthData.Bq 5160 = (251839458226794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5160 = 251839458226794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5160 = (329:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5161) ≤ val WuPaper.ClassicalFourthData.Bq 5161
    have hp : val WuPaper.ClassicalFourthData.Bq 5161 = (251853501075354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5161 = 251853501075354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5161 = (13161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5162) ≤ val WuPaper.ClassicalFourthData.Bq 5162
    have hp : val WuPaper.ClassicalFourthData.Bq 5162 = (251867538168869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5162 = 251867538168869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5162 = (6581:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5163) ≤ val WuPaper.ClassicalFourthData.Bq 5163
    have hp : val WuPaper.ClassicalFourthData.Bq 5163 = (251881569509440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5163 = 251881569509440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5163 = (13163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5164) ≤ val WuPaper.ClassicalFourthData.Bq 5164
    have hp : val WuPaper.ClassicalFourthData.Bq 5164 = (251895595099168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5164 = 251895595099168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5164 = (3291:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5165) ≤ val WuPaper.ClassicalFourthData.Bq 5165
    have hp : val WuPaper.ClassicalFourthData.Bq 5165 = (251909614940154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5165 = 251909614940154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5165 = (2633:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5166) ≤ val WuPaper.ClassicalFourthData.Bq 5166
    have hp : val WuPaper.ClassicalFourthData.Bq 5166 = (251923629034496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5166 = 251923629034496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5166 = (6583:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5167) ≤ val WuPaper.ClassicalFourthData.Bq 5167
    have hp : val WuPaper.ClassicalFourthData.Bq 5167 = (251937637384294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5167 = 251937637384294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5167 = (13167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_322
