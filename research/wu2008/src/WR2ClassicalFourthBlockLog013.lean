import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints013
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_013 (j : Fin 16) (hj : 16*13+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*13+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*13+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 208) ≤ val WuPaper.ClassicalFourthData.Bq 208
    have hp : val WuPaper.ClassicalFourthData.Bq 208 = (24704246742456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 208 = 24704246742456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 208 = (513:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 209) ≤ val WuPaper.ClassicalFourthData.Bq 209
    have hp : val WuPaper.ClassicalFourthData.Bq 209 = (24817019694747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 209 = 24817019694747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 209 = (8209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 210) ≤ val WuPaper.ClassicalFourthData.Bq 210
    have hp : val WuPaper.ClassicalFourthData.Bq 210 = (24929737673277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 210 = 24929737673277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 210 = (821:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 211) ≤ val WuPaper.ClassicalFourthData.Bq 211
    have hp : val WuPaper.ClassicalFourthData.Bq 211 = (25042400711193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 211 = 25042400711193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 211 = (8211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 212) ≤ val WuPaper.ClassicalFourthData.Bq 212
    have hp : val WuPaper.ClassicalFourthData.Bq 212 = (25155008841617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 212 = 25155008841617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 212 = (2053:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 213) ≤ val WuPaper.ClassicalFourthData.Bq 213
    have hp : val WuPaper.ClassicalFourthData.Bq 213 = (25267562097645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 213 = 25267562097645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 213 = (8213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 214) ≤ val WuPaper.ClassicalFourthData.Bq 214
    have hp : val WuPaper.ClassicalFourthData.Bq 214 = (25380060512349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 214 = 25380060512349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 214 = (4107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 215) ≤ val WuPaper.ClassicalFourthData.Bq 215
    have hp : val WuPaper.ClassicalFourthData.Bq 215 = (25492504118773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 215 = 25492504118773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 215 = (1643:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 216) ≤ val WuPaper.ClassicalFourthData.Bq 216
    have hp : val WuPaper.ClassicalFourthData.Bq 216 = (25604892949937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 216 = 25604892949937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 216 = (1027:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 217) ≤ val WuPaper.ClassicalFourthData.Bq 217
    have hp : val WuPaper.ClassicalFourthData.Bq 217 = (25717227038838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 217 = 25717227038838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 217 = (8217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 218) ≤ val WuPaper.ClassicalFourthData.Bq 218
    have hp : val WuPaper.ClassicalFourthData.Bq 218 = (25829506418444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 218 = 25829506418444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 218 = (4109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 219) ≤ val WuPaper.ClassicalFourthData.Bq 219
    have hp : val WuPaper.ClassicalFourthData.Bq 219 = (25941731121699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 219 = 25941731121699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 219 = (8219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 220) ≤ val WuPaper.ClassicalFourthData.Bq 220
    have hp : val WuPaper.ClassicalFourthData.Bq 220 = (26053901181524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 220 = 26053901181524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 220 = (411:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 221) ≤ val WuPaper.ClassicalFourthData.Bq 221
    have hp : val WuPaper.ClassicalFourthData.Bq 221 = (26166016630810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 221 = 26166016630810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 221 = (8221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 222) ≤ val WuPaper.ClassicalFourthData.Bq 222
    have hp : val WuPaper.ClassicalFourthData.Bq 222 = (26278077502427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 222 = 26278077502427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 222 = (4111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 223) ≤ val WuPaper.ClassicalFourthData.Bq 223
    have hp : val WuPaper.ClassicalFourthData.Bq 223 = (26390083829219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 223 = 26390083829219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 223 = (8223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_013
