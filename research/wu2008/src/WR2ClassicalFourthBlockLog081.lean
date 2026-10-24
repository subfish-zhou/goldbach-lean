import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints081
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_081 (j : Fin 16) (hj : 16*81+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*81+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*81+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1296) ≤ val WuPaper.ClassicalFourthData.Bq 1296
    have hp : val WuPaper.ClassicalFourthData.Bq 1296 = (120764826813605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1296 = 120764826813605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1296 = (581:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1297) ≤ val WuPaper.ClassicalFourthData.Bq 1297
    have hp : val WuPaper.ClassicalFourthData.Bq 1297 = (120833069352479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1297 = 120833069352479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1297 = (9297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1298) ≤ val WuPaper.ClassicalFourthData.Bq 1298
    have hp : val WuPaper.ClassicalFourthData.Bq 1298 = (120901281879969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1298 = 120901281879969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1298 = (4649:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1299) ≤ val WuPaper.ClassicalFourthData.Bq 1299
    have hp : val WuPaper.ClassicalFourthData.Bq 1299 = (120969464411543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1299 = 120969464411543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1299 = (9299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1300) ≤ val WuPaper.ClassicalFourthData.Bq 1300
    have hp : val WuPaper.ClassicalFourthData.Bq 1300 = (121037616962661:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1300 = 121037616962661 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1300 = (93:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1301) ≤ val WuPaper.ClassicalFourthData.Bq 1301
    have hp : val WuPaper.ClassicalFourthData.Bq 1301 = (121105739548771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1301 = 121105739548771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1301 = (9301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1302) ≤ val WuPaper.ClassicalFourthData.Bq 1302
    have hp : val WuPaper.ClassicalFourthData.Bq 1302 = (121173832185313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1302 = 121173832185313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1302 = (4651:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1303) ≤ val WuPaper.ClassicalFourthData.Bq 1303
    have hp : val WuPaper.ClassicalFourthData.Bq 1303 = (121241894887715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1303 = 121241894887715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1303 = (9303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1303
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1304) ≤ val WuPaper.ClassicalFourthData.Bq 1304
    have hp : val WuPaper.ClassicalFourthData.Bq 1304 = (121309927671398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1304 = 121309927671398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1304 = (1163:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1305) ≤ val WuPaper.ClassicalFourthData.Bq 1305
    have hp : val WuPaper.ClassicalFourthData.Bq 1305 = (121377930551771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1305 = 121377930551771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1305 = (1861:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1306) ≤ val WuPaper.ClassicalFourthData.Bq 1306
    have hp : val WuPaper.ClassicalFourthData.Bq 1306 = (121445903544233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1306 = 121445903544233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1306 = (4653:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1307) ≤ val WuPaper.ClassicalFourthData.Bq 1307
    have hp : val WuPaper.ClassicalFourthData.Bq 1307 = (121513846664175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1307 = 121513846664175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1307 = (9307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1308) ≤ val WuPaper.ClassicalFourthData.Bq 1308
    have hp : val WuPaper.ClassicalFourthData.Bq 1308 = (121581759926975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1308 = 121581759926975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1308 = (2327:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1309) ≤ val WuPaper.ClassicalFourthData.Bq 1309
    have hp : val WuPaper.ClassicalFourthData.Bq 1309 = (121649643348005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1309 = 121649643348005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1309 = (9309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1310) ≤ val WuPaper.ClassicalFourthData.Bq 1310
    have hp : val WuPaper.ClassicalFourthData.Bq 1310 = (121717496942624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1310 = 121717496942624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1310 = (931:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1311) ≤ val WuPaper.ClassicalFourthData.Bq 1311
    have hp : val WuPaper.ClassicalFourthData.Bq 1311 = (121785320726183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1311 = 121785320726183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1311 = (9311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_081
