import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints080
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_080 (j : Fin 16) (hj : 16*80+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*80+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*80+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1280) ≤ val WuPaper.ClassicalFourthData.Bq 1280
    have hp : val WuPaper.ClassicalFourthData.Bq 1280 = (119668851982018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1280 = 119668851982018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1280 = (58:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1281) ≤ val WuPaper.ClassicalFourthData.Bq 1281
    have hp : val WuPaper.ClassicalFourthData.Bq 1281 = (119737576814958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1281 = 119737576814958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1281 = (9281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1282) ≤ val WuPaper.ClassicalFourthData.Bq 1282
    have hp : val WuPaper.ClassicalFourthData.Bq 1282 = (119806271387654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1282 = 119806271387654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1282 = (4641:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1283) ≤ val WuPaper.ClassicalFourthData.Bq 1283
    have hp : val WuPaper.ClassicalFourthData.Bq 1283 = (119874935715734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1283 = 119874935715734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1283 = (9283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1284) ≤ val WuPaper.ClassicalFourthData.Bq 1284
    have hp : val WuPaper.ClassicalFourthData.Bq 1284 = (119943569814817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1284 = 119943569814817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1284 = (2321:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1285) ≤ val WuPaper.ClassicalFourthData.Bq 1285
    have hp : val WuPaper.ClassicalFourthData.Bq 1285 = (120012173700511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1285 = 120012173700511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1285 = (1857:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1286) ≤ val WuPaper.ClassicalFourthData.Bq 1286
    have hp : val WuPaper.ClassicalFourthData.Bq 1286 = (120080747388416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1286 = 120080747388416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1286 = (4643:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1287) ≤ val WuPaper.ClassicalFourthData.Bq 1287
    have hp : val WuPaper.ClassicalFourthData.Bq 1287 = (120149290894120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1287 = 120149290894120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1287 = (9287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1287
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1288) ≤ val WuPaper.ClassicalFourthData.Bq 1288
    have hp : val WuPaper.ClassicalFourthData.Bq 1288 = (120217804233202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1288 = 120217804233202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1288 = (1161:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1289) ≤ val WuPaper.ClassicalFourthData.Bq 1289
    have hp : val WuPaper.ClassicalFourthData.Bq 1289 = (120286287421231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1289 = 120286287421231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1289 = (9289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1290) ≤ val WuPaper.ClassicalFourthData.Bq 1290
    have hp : val WuPaper.ClassicalFourthData.Bq 1290 = (120354740473765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1290 = 120354740473765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1290 = (929:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1291) ≤ val WuPaper.ClassicalFourthData.Bq 1291
    have hp : val WuPaper.ClassicalFourthData.Bq 1291 = (120423163406352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1291 = 120423163406352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1291 = (9291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1292) ≤ val WuPaper.ClassicalFourthData.Bq 1292
    have hp : val WuPaper.ClassicalFourthData.Bq 1292 = (120491556234533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1292 = 120491556234533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1292 = (2323:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1293) ≤ val WuPaper.ClassicalFourthData.Bq 1293
    have hp : val WuPaper.ClassicalFourthData.Bq 1293 = (120559918973835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1293 = 120559918973835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1293 = (9293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1294) ≤ val WuPaper.ClassicalFourthData.Bq 1294
    have hp : val WuPaper.ClassicalFourthData.Bq 1294 = (120628251639776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1294 = 120628251639776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1294 = (4647:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1295) ≤ val WuPaper.ClassicalFourthData.Bq 1295
    have hp : val WuPaper.ClassicalFourthData.Bq 1295 = (120696554247867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1295 = 120696554247867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1295 = (1859:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_080
