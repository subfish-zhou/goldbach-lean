import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints326
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_326 (j : Fin 16) (hj : 16*326+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*326+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*326+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5216) ≤ val WuPaper.ClassicalFourthData.Bq 5216
    have hp : val WuPaper.ClassicalFourthData.Bq 5216 = (252617052915753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5216 = 252617052915753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5216 = (413:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5217) ≤ val WuPaper.ClassicalFourthData.Bq 5217
    have hp : val WuPaper.ClassicalFourthData.Bq 5217 = (252630776694148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5217 = 252630776694148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5217 = (13217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5218) ≤ val WuPaper.ClassicalFourthData.Bq 5218
    have hp : val WuPaper.ClassicalFourthData.Bq 5218 = (252644494833841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5218 = 252644494833841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5218 = (6609:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5219) ≤ val WuPaper.ClassicalFourthData.Bq 5219
    have hp : val WuPaper.ClassicalFourthData.Bq 5219 = (252658207336885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5219 = 252658207336885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5219 = (13219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5220) ≤ val WuPaper.ClassicalFourthData.Bq 5220
    have hp : val WuPaper.ClassicalFourthData.Bq 5220 = (252671914205330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5220 = 252671914205330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5220 = (661:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5221) ≤ val WuPaper.ClassicalFourthData.Bq 5221
    have hp : val WuPaper.ClassicalFourthData.Bq 5221 = (252685615441227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5221 = 252685615441227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5221 = (13221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5222) ≤ val WuPaper.ClassicalFourthData.Bq 5222
    have hp : val WuPaper.ClassicalFourthData.Bq 5222 = (252699311046627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5222 = 252699311046627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5222 = (6611:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5223) ≤ val WuPaper.ClassicalFourthData.Bq 5223
    have hp : val WuPaper.ClassicalFourthData.Bq 5223 = (252713001023578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5223 = 252713001023578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5223 = (13223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5223
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5224) ≤ val WuPaper.ClassicalFourthData.Bq 5224
    have hp : val WuPaper.ClassicalFourthData.Bq 5224 = (252726685374129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5224 = 252726685374129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5224 = (1653:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5225) ≤ val WuPaper.ClassicalFourthData.Bq 5225
    have hp : val WuPaper.ClassicalFourthData.Bq 5225 = (252740364100326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5225 = 252740364100326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5225 = (529:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5226) ≤ val WuPaper.ClassicalFourthData.Bq 5226
    have hp : val WuPaper.ClassicalFourthData.Bq 5226 = (252754037204216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5226 = 252754037204216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5226 = (6613:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5227) ≤ val WuPaper.ClassicalFourthData.Bq 5227
    have hp : val WuPaper.ClassicalFourthData.Bq 5227 = (252767704687845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5227 = 252767704687845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5227 = (13227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5228) ≤ val WuPaper.ClassicalFourthData.Bq 5228
    have hp : val WuPaper.ClassicalFourthData.Bq 5228 = (252781366553257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5228 = 252781366553257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5228 = (3307:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5229) ≤ val WuPaper.ClassicalFourthData.Bq 5229
    have hp : val WuPaper.ClassicalFourthData.Bq 5229 = (252795022802495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5229 = 252795022802495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5229 = (13229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5230) ≤ val WuPaper.ClassicalFourthData.Bq 5230
    have hp : val WuPaper.ClassicalFourthData.Bq 5230 = (252808673437603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5230 = 252808673437603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5230 = (1323:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5231) ≤ val WuPaper.ClassicalFourthData.Bq 5231
    have hp : val WuPaper.ClassicalFourthData.Bq 5231 = (252822318460623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5231 = 252822318460623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5231 = (13231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_326
