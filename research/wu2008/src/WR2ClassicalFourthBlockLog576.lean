import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints576
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_576 (j : Fin 16) (hj : 16*576+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*576+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*576+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9216) ≤ val WuPaper.ClassicalFourthData.Bq 9216
    have hp : val WuPaper.ClassicalFourthData.Bq 9216 = (277679799183290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9216 = 277679799183290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9216 = (538:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9217) ≤ val WuPaper.ClassicalFourthData.Bq 9217
    have hp : val WuPaper.ClassicalFourthData.Bq 9217 = (277681249621182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9217 = 277681249621182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9217 = (17217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9218) ≤ val WuPaper.ClassicalFourthData.Bq 9218
    have hp : val WuPaper.ClassicalFourthData.Bq 9218 = (277682698560718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9218 = 277682698560718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9218 = (8609:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9219) ≤ val WuPaper.ClassicalFourthData.Bq 9219
    have hp : val WuPaper.ClassicalFourthData.Bq 9219 = (277684146002360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9219 = 277684146002360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9219 = (17219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9220) ≤ val WuPaper.ClassicalFourthData.Bq 9220
    have hp : val WuPaper.ClassicalFourthData.Bq 9220 = (277685591946570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9220 = 277685591946570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9220 = (861:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9221) ≤ val WuPaper.ClassicalFourthData.Bq 9221
    have hp : val WuPaper.ClassicalFourthData.Bq 9221 = (277687036393809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9221 = 277687036393809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9221 = (17221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9222) ≤ val WuPaper.ClassicalFourthData.Bq 9222
    have hp : val WuPaper.ClassicalFourthData.Bq 9222 = (277688479344541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9222 = 277688479344541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9222 = (8611:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9223) ≤ val WuPaper.ClassicalFourthData.Bq 9223
    have hp : val WuPaper.ClassicalFourthData.Bq 9223 = (277689920799226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9223 = 277689920799226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9223 = (17223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9223
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9224) ≤ val WuPaper.ClassicalFourthData.Bq 9224
    have hp : val WuPaper.ClassicalFourthData.Bq 9224 = (277691360758325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9224 = 277691360758325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9224 = (2153:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9225) ≤ val WuPaper.ClassicalFourthData.Bq 9225
    have hp : val WuPaper.ClassicalFourthData.Bq 9225 = (277692799222301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9225 = 277692799222301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9225 = (689:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9226) ≤ val WuPaper.ClassicalFourthData.Bq 9226
    have hp : val WuPaper.ClassicalFourthData.Bq 9226 = (277694236191615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9226 = 277694236191615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9226 = (8613:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9227) ≤ val WuPaper.ClassicalFourthData.Bq 9227
    have hp : val WuPaper.ClassicalFourthData.Bq 9227 = (277695671666727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9227 = 277695671666727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9227 = (17227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9228) ≤ val WuPaper.ClassicalFourthData.Bq 9228
    have hp : val WuPaper.ClassicalFourthData.Bq 9228 = (277697105648098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9228 = 277697105648098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9228 = (4307:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9229) ≤ val WuPaper.ClassicalFourthData.Bq 9229
    have hp : val WuPaper.ClassicalFourthData.Bq 9229 = (277698538136189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9229 = 277698538136189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9229 = (17229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9230) ≤ val WuPaper.ClassicalFourthData.Bq 9230
    have hp : val WuPaper.ClassicalFourthData.Bq 9230 = (277699969131461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9230 = 277699969131461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9230 = (1723:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9231) ≤ val WuPaper.ClassicalFourthData.Bq 9231
    have hp : val WuPaper.ClassicalFourthData.Bq 9231 = (277701398634374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9231 = 277701398634374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9231 = (17231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_576
