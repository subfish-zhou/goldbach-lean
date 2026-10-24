import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints643
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_643 (j : Fin 16) (hj : 16*643+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*643+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*643+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10288) ≤ val WuPaper.ClassicalFourthData.Bq 10288
    have hp : val WuPaper.ClassicalFourthData.Bq 10288 = (278461431137837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10288 = 278461431137837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10288 = (1143:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10289) ≤ val WuPaper.ClassicalFourthData.Bq 10289
    have hp : val WuPaper.ClassicalFourthData.Bq 10289 = (278461512278441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10289 = 278461512278441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10289 = (18289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10290) ≤ val WuPaper.ClassicalFourthData.Bq 10290
    have hp : val WuPaper.ClassicalFourthData.Bq 10290 = (278461592339042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10290 = 278461592339042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10290 = (1829:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10291) ≤ val WuPaper.ClassicalFourthData.Bq 10291
    have hp : val WuPaper.ClassicalFourthData.Bq 10291 = (278461671319965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10291 = 278461671319965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10291 = (18291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10292) ≤ val WuPaper.ClassicalFourthData.Bq 10292
    have hp : val WuPaper.ClassicalFourthData.Bq 10292 = (278461749221540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10292 = 278461749221540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10292 = (4573:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10293) ≤ val WuPaper.ClassicalFourthData.Bq 10293
    have hp : val WuPaper.ClassicalFourthData.Bq 10293 = (278461826044091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10293 = 278461826044091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10293 = (18293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10294) ≤ val WuPaper.ClassicalFourthData.Bq 10294
    have hp : val WuPaper.ClassicalFourthData.Bq 10294 = (278461901787946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10294 = 278461901787946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10294 = (9147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10295) ≤ val WuPaper.ClassicalFourthData.Bq 10295
    have hp : val WuPaper.ClassicalFourthData.Bq 10295 = (278461976453432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10295 = 278461976453432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10295 = (3659:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10296) ≤ val WuPaper.ClassicalFourthData.Bq 10296
    have hp : val WuPaper.ClassicalFourthData.Bq 10296 = (278462050040874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10296 = 278462050040874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10296 = (2287:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10297) ≤ val WuPaper.ClassicalFourthData.Bq 10297
    have hp : val WuPaper.ClassicalFourthData.Bq 10297 = (278462122550600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10297 = 278462122550600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10297 = (18297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10298) ≤ val WuPaper.ClassicalFourthData.Bq 10298
    have hp : val WuPaper.ClassicalFourthData.Bq 10298 = (278462193982936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10298 = 278462193982936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10298 = (9149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10299) ≤ val WuPaper.ClassicalFourthData.Bq 10299
    have hp : val WuPaper.ClassicalFourthData.Bq 10299 = (278462264338208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10299 = 278462264338208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10299 = (18299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10300) ≤ val WuPaper.ClassicalFourthData.Bq 10300
    have hp : val WuPaper.ClassicalFourthData.Bq 10300 = (278462333616742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10300 = 278462333616742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10300 = (183:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10301) ≤ val WuPaper.ClassicalFourthData.Bq 10301
    have hp : val WuPaper.ClassicalFourthData.Bq 10301 = (278462401818864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10301 = 278462401818864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10301 = (18301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10302) ≤ val WuPaper.ClassicalFourthData.Bq 10302
    have hp : val WuPaper.ClassicalFourthData.Bq 10302 = (278462468944900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10302 = 278462468944900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10302 = (9151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10303) ≤ val WuPaper.ClassicalFourthData.Bq 10303
    have hp : val WuPaper.ClassicalFourthData.Bq 10303 = (278462534995175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10303 = 278462534995175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10303 = (18303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_643
