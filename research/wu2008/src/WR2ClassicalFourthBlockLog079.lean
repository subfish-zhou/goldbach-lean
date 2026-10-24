import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints079
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_079 (j : Fin 16) (hj : 16*79+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*79+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*79+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1264) ≤ val WuPaper.ClassicalFourthData.Bq 1264
    have hp : val WuPaper.ClassicalFourthData.Bq 1264 = (118565126469398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1264 = 118565126469398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1264 = (579:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1265) ≤ val WuPaper.ClassicalFourthData.Bq 1265
    have hp : val WuPaper.ClassicalFourthData.Bq 1265 = (118634337600021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1265 = 118634337600021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1265 = (1853:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1266) ≤ val WuPaper.ClassicalFourthData.Bq 1266
    have hp : val WuPaper.ClassicalFourthData.Bq 1266 = (118703518218963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1266 = 118703518218963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1266 = (4633:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1267) ≤ val WuPaper.ClassicalFourthData.Bq 1267
    have hp : val WuPaper.ClassicalFourthData.Bq 1267 = (118772668342015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1267 = 118772668342015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1267 = (9267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1268) ≤ val WuPaper.ClassicalFourthData.Bq 1268
    have hp : val WuPaper.ClassicalFourthData.Bq 1268 = (118841787984957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1268 = 118841787984957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1268 = (2317:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1269) ≤ val WuPaper.ClassicalFourthData.Bq 1269
    have hp : val WuPaper.ClassicalFourthData.Bq 1269 = (118910877163560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1269 = 118910877163560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1269 = (9269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1270) ≤ val WuPaper.ClassicalFourthData.Bq 1270
    have hp : val WuPaper.ClassicalFourthData.Bq 1270 = (118979935893584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1270 = 118979935893584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1270 = (927:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1271) ≤ val WuPaper.ClassicalFourthData.Bq 1271
    have hp : val WuPaper.ClassicalFourthData.Bq 1271 = (119048964190780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1271 = 119048964190780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1271 = (9271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1271
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1272) ≤ val WuPaper.ClassicalFourthData.Bq 1272
    have hp : val WuPaper.ClassicalFourthData.Bq 1272 = (119117962070887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1272 = 119117962070887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1272 = (1159:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1273) ≤ val WuPaper.ClassicalFourthData.Bq 1273
    have hp : val WuPaper.ClassicalFourthData.Bq 1273 = (119186929549636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1273 = 119186929549636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1273 = (9273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1274) ≤ val WuPaper.ClassicalFourthData.Bq 1274
    have hp : val WuPaper.ClassicalFourthData.Bq 1274 = (119255866642746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1274 = 119255866642746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1274 = (4637:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1275) ≤ val WuPaper.ClassicalFourthData.Bq 1275
    have hp : val WuPaper.ClassicalFourthData.Bq 1275 = (119324773365926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1275 = 119324773365926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1275 = (371:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1276) ≤ val WuPaper.ClassicalFourthData.Bq 1276
    have hp : val WuPaper.ClassicalFourthData.Bq 1276 = (119393649734877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1276 = 119393649734877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1276 = (2319:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1277) ≤ val WuPaper.ClassicalFourthData.Bq 1277
    have hp : val WuPaper.ClassicalFourthData.Bq 1277 = (119462495765287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1277 = 119462495765287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1277 = (9277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1278) ≤ val WuPaper.ClassicalFourthData.Bq 1278
    have hp : val WuPaper.ClassicalFourthData.Bq 1278 = (119531311472836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1278 = 119531311472836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1278 = (4639:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1279) ≤ val WuPaper.ClassicalFourthData.Bq 1279
    have hp : val WuPaper.ClassicalFourthData.Bq 1279 = (119600096873193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1279 = 119600096873193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1279 = (9279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_079
