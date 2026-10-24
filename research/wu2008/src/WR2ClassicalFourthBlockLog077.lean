import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints077
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_077 (j : Fin 16) (hj : 16*77+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*77+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*77+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1232) ≤ val WuPaper.ClassicalFourthData.Bq 1232
    have hp : val WuPaper.ClassicalFourthData.Bq 1232 = (116334165093158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1232 = 116334165093158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1232 = (577:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1232
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1233) ≤ val WuPaper.ClassicalFourthData.Bq 1233
    have hp : val WuPaper.ClassicalFourthData.Bq 1233 = (116404360996504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1233 = 116404360996504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1233 = (9233:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1233
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1234) ≤ val WuPaper.ClassicalFourthData.Bq 1234
    have hp : val WuPaper.ClassicalFourthData.Bq 1234 = (116474525877438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1234 = 116474525877438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1234 = (4617:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1234
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1235) ≤ val WuPaper.ClassicalFourthData.Bq 1235
    have hp : val WuPaper.ClassicalFourthData.Bq 1235 = (116544659752078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1235 = 116544659752078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1235 = (1847:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1235
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1236) ≤ val WuPaper.ClassicalFourthData.Bq 1236
    have hp : val WuPaper.ClassicalFourthData.Bq 1236 = (116614762636537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1236 = 116614762636537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1236 = (2309:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1236
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1237) ≤ val WuPaper.ClassicalFourthData.Bq 1237
    have hp : val WuPaper.ClassicalFourthData.Bq 1237 = (116684834546914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1237 = 116684834546914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1237 = (9237:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1237
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1238) ≤ val WuPaper.ClassicalFourthData.Bq 1238
    have hp : val WuPaper.ClassicalFourthData.Bq 1238 = (116754875499299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1238 = 116754875499299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1238 = (4619:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1238
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1239) ≤ val WuPaper.ClassicalFourthData.Bq 1239
    have hp : val WuPaper.ClassicalFourthData.Bq 1239 = (116824885509771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1239 = 116824885509771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1239 = (9239:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1239
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1240) ≤ val WuPaper.ClassicalFourthData.Bq 1240
    have hp : val WuPaper.ClassicalFourthData.Bq 1240 = (116894864594399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1240 = 116894864594399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1240 = (231:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1240
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1241) ≤ val WuPaper.ClassicalFourthData.Bq 1241
    have hp : val WuPaper.ClassicalFourthData.Bq 1241 = (116964812769241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1241 = 116964812769241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1241 = (9241:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1241
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1242) ≤ val WuPaper.ClassicalFourthData.Bq 1242
    have hp : val WuPaper.ClassicalFourthData.Bq 1242 = (117034730050346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1242 = 117034730050346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1242 = (4621:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1242
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1243) ≤ val WuPaper.ClassicalFourthData.Bq 1243
    have hp : val WuPaper.ClassicalFourthData.Bq 1243 = (117104616453751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1243 = 117104616453751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1243 = (9243:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1243
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1244) ≤ val WuPaper.ClassicalFourthData.Bq 1244
    have hp : val WuPaper.ClassicalFourthData.Bq 1244 = (117174471995484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1244 = 117174471995484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1244 = (2311:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1244
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1245) ≤ val WuPaper.ClassicalFourthData.Bq 1245
    have hp : val WuPaper.ClassicalFourthData.Bq 1245 = (117244296691561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1245 = 117244296691561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1245 = (1849:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1245
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1246) ≤ val WuPaper.ClassicalFourthData.Bq 1246
    have hp : val WuPaper.ClassicalFourthData.Bq 1246 = (117314090557989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1246 = 117314090557989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1246 = (4623:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1246
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1247) ≤ val WuPaper.ClassicalFourthData.Bq 1247
    have hp : val WuPaper.ClassicalFourthData.Bq 1247 = (117383853610765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1247 = 117383853610765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1247 = (9247:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1247
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_077
