import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints450
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_450 (j : Fin 16) (hj : 16*450+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*450+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*450+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7200) ≤ val WuPaper.ClassicalFourthData.Bq 7200
    have hp : val WuPaper.ClassicalFourthData.Bq 7200 = (270952478205679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7200 = 270952478205679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7200 = (19:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7201) ≤ val WuPaper.ClassicalFourthData.Bq 7201
    have hp : val WuPaper.ClassicalFourthData.Bq 7201 = (270958147203509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7201 = 270958147203509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7201 = (15201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7202) ≤ val WuPaper.ClassicalFourthData.Bq 7202
    have hp : val WuPaper.ClassicalFourthData.Bq 7202 = (270963813358288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7202 = 270963813358288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7202 = (7601:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7203) ≤ val WuPaper.ClassicalFourthData.Bq 7203
    have hp : val WuPaper.ClassicalFourthData.Bq 7203 = (270969476670952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7203 = 270969476670952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7203 = (15203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7204) ≤ val WuPaper.ClassicalFourthData.Bq 7204
    have hp : val WuPaper.ClassicalFourthData.Bq 7204 = (270975137142436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7204 = 270975137142436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7204 = (3801:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7205) ≤ val WuPaper.ClassicalFourthData.Bq 7205
    have hp : val WuPaper.ClassicalFourthData.Bq 7205 = (270980794773674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7205 = 270980794773674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7205 = (3041:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7206) ≤ val WuPaper.ClassicalFourthData.Bq 7206
    have hp : val WuPaper.ClassicalFourthData.Bq 7206 = (270986449565601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7206 = 270986449565601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7206 = (7603:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7207) ≤ val WuPaper.ClassicalFourthData.Bq 7207
    have hp : val WuPaper.ClassicalFourthData.Bq 7207 = (270992101519150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7207 = 270992101519150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7207 = (15207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7207
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7208) ≤ val WuPaper.ClassicalFourthData.Bq 7208
    have hp : val WuPaper.ClassicalFourthData.Bq 7208 = (270997750635257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7208 = 270997750635257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7208 = (1901:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7209) ≤ val WuPaper.ClassicalFourthData.Bq 7209
    have hp : val WuPaper.ClassicalFourthData.Bq 7209 = (271003396914853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7209 = 271003396914853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7209 = (15209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7210) ≤ val WuPaper.ClassicalFourthData.Bq 7210
    have hp : val WuPaper.ClassicalFourthData.Bq 7210 = (271009040358872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7210 = 271009040358872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7210 = (1521:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7211) ≤ val WuPaper.ClassicalFourthData.Bq 7211
    have hp : val WuPaper.ClassicalFourthData.Bq 7211 = (271014680968247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7211 = 271014680968247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7211 = (15211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7212) ≤ val WuPaper.ClassicalFourthData.Bq 7212
    have hp : val WuPaper.ClassicalFourthData.Bq 7212 = (271020318743909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7212 = 271020318743909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7212 = (3803:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7213) ≤ val WuPaper.ClassicalFourthData.Bq 7213
    have hp : val WuPaper.ClassicalFourthData.Bq 7213 = (271025953686791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7213 = 271025953686791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7213 = (15213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7214) ≤ val WuPaper.ClassicalFourthData.Bq 7214
    have hp : val WuPaper.ClassicalFourthData.Bq 7214 = (271031585797825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7214 = 271031585797825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7214 = (7607:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7215) ≤ val WuPaper.ClassicalFourthData.Bq 7215
    have hp : val WuPaper.ClassicalFourthData.Bq 7215 = (271037215077941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7215 = 271037215077941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7215 = (3043:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_450
