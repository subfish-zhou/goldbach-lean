import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints640
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_640 (j : Fin 16) (hj : 16*640+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*640+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*640+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10240) ≤ val WuPaper.ClassicalFourthData.Bq 10240
    have hp : val WuPaper.ClassicalFourthData.Bq 10240 = (278456259868764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10240 = 278456259868764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10240 = (114:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10241) ≤ val WuPaper.ClassicalFourthData.Bq 10241
    have hp : val WuPaper.ClassicalFourthData.Bq 10241 = (278456393236168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10241 = 278456393236168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10241 = (18241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10242) ≤ val WuPaper.ClassicalFourthData.Bq 10242
    have hp : val WuPaper.ClassicalFourthData.Bq 10242 = (278456525507748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10242 = 278456525507748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10242 = (9121:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10243) ≤ val WuPaper.ClassicalFourthData.Bq 10243
    have hp : val WuPaper.ClassicalFourthData.Bq 10243 = (278456656683837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10243 = 278456656683837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10243 = (18243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10244) ≤ val WuPaper.ClassicalFourthData.Bq 10244
    have hp : val WuPaper.ClassicalFourthData.Bq 10244 = (278456786764767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10244 = 278456786764767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10244 = (4561:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10245) ≤ val WuPaper.ClassicalFourthData.Bq 10245
    have hp : val WuPaper.ClassicalFourthData.Bq 10245 = (278456915750869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10245 = 278456915750869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10245 = (3649:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10246) ≤ val WuPaper.ClassicalFourthData.Bq 10246
    have hp : val WuPaper.ClassicalFourthData.Bq 10246 = (278457043642475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10246 = 278457043642475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10246 = (9123:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10247) ≤ val WuPaper.ClassicalFourthData.Bq 10247
    have hp : val WuPaper.ClassicalFourthData.Bq 10247 = (278457170439917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10247 = 278457170439917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10247 = (18247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10247
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10248) ≤ val WuPaper.ClassicalFourthData.Bq 10248
    have hp : val WuPaper.ClassicalFourthData.Bq 10248 = (278457296143526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10248 = 278457296143526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10248 = (2281:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10249) ≤ val WuPaper.ClassicalFourthData.Bq 10249
    have hp : val WuPaper.ClassicalFourthData.Bq 10249 = (278457420753634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10249 = 278457420753634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10249 = (18249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10250) ≤ val WuPaper.ClassicalFourthData.Bq 10250
    have hp : val WuPaper.ClassicalFourthData.Bq 10250 = (278457544270573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10250 = 278457544270573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10250 = (73:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10251) ≤ val WuPaper.ClassicalFourthData.Bq 10251
    have hp : val WuPaper.ClassicalFourthData.Bq 10251 = (278457666694672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10251 = 278457666694672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10251 = (18251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10252) ≤ val WuPaper.ClassicalFourthData.Bq 10252
    have hp : val WuPaper.ClassicalFourthData.Bq 10252 = (278457788026263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10252 = 278457788026263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10252 = (4563:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10253) ≤ val WuPaper.ClassicalFourthData.Bq 10253
    have hp : val WuPaper.ClassicalFourthData.Bq 10253 = (278457908265678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10253 = 278457908265678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10253 = (18253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10254) ≤ val WuPaper.ClassicalFourthData.Bq 10254
    have hp : val WuPaper.ClassicalFourthData.Bq 10254 = (278458027413247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10254 = 278458027413247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10254 = (9127:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10255) ≤ val WuPaper.ClassicalFourthData.Bq 10255
    have hp : val WuPaper.ClassicalFourthData.Bq 10255 = (278458145469301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10255 = 278458145469301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10255 = (3651:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10255
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_640
