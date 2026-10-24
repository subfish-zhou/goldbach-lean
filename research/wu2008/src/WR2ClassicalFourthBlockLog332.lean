import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints332
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_332 (j : Fin 16) (hj : 16*332+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*332+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*332+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5312) ≤ val WuPaper.ClassicalFourthData.Bq 5312
    have hp : val WuPaper.ClassicalFourthData.Bq 5312 = (253909113542426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5312 = 253909113542426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5312 = (416:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5313) ≤ val WuPaper.ClassicalFourthData.Bq 5313
    have hp : val WuPaper.ClassicalFourthData.Bq 5313 = (253922305241383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5313 = 253922305241383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5313 = (13313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5314) ≤ val WuPaper.ClassicalFourthData.Bq 5314
    have hp : val WuPaper.ClassicalFourthData.Bq 5314 = (253935491494757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5314 = 253935491494757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5314 = (6657:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5315) ≤ val WuPaper.ClassicalFourthData.Bq 5315
    have hp : val WuPaper.ClassicalFourthData.Bq 5315 = (253948672304518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5315 = 253948672304518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5315 = (2663:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5316) ≤ val WuPaper.ClassicalFourthData.Bq 5316
    have hp : val WuPaper.ClassicalFourthData.Bq 5316 = (253961847672637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5316 = 253961847672637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5316 = (3329:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5317) ≤ val WuPaper.ClassicalFourthData.Bq 5317
    have hp : val WuPaper.ClassicalFourthData.Bq 5317 = (253975017601082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5317 = 253975017601082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5317 = (13317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5318) ≤ val WuPaper.ClassicalFourthData.Bq 5318
    have hp : val WuPaper.ClassicalFourthData.Bq 5318 = (253988182091821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5318 = 253988182091821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5318 = (6659:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5319) ≤ val WuPaper.ClassicalFourthData.Bq 5319
    have hp : val WuPaper.ClassicalFourthData.Bq 5319 = (254001341146822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5319 = 254001341146822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5319 = (13319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5319
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5320) ≤ val WuPaper.ClassicalFourthData.Bq 5320
    have hp : val WuPaper.ClassicalFourthData.Bq 5320 = (254014494768052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5320 = 254014494768052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5320 = (333:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5321) ≤ val WuPaper.ClassicalFourthData.Bq 5321
    have hp : val WuPaper.ClassicalFourthData.Bq 5321 = (254027642957476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5321 = 254027642957476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5321 = (13321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5322) ≤ val WuPaper.ClassicalFourthData.Bq 5322
    have hp : val WuPaper.ClassicalFourthData.Bq 5322 = (254040785717058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5322 = 254040785717058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5322 = (6661:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5323) ≤ val WuPaper.ClassicalFourthData.Bq 5323
    have hp : val WuPaper.ClassicalFourthData.Bq 5323 = (254053923048764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5323 = 254053923048764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5323 = (13323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5324) ≤ val WuPaper.ClassicalFourthData.Bq 5324
    have hp : val WuPaper.ClassicalFourthData.Bq 5324 = (254067054954555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5324 = 254067054954555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5324 = (3331:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5325) ≤ val WuPaper.ClassicalFourthData.Bq 5325
    have hp : val WuPaper.ClassicalFourthData.Bq 5325 = (254080181436395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5325 = 254080181436395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5325 = (533:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5326) ≤ val WuPaper.ClassicalFourthData.Bq 5326
    have hp : val WuPaper.ClassicalFourthData.Bq 5326 = (254093302496246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5326 = 254093302496246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5326 = (6663:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5327) ≤ val WuPaper.ClassicalFourthData.Bq 5327
    have hp : val WuPaper.ClassicalFourthData.Bq 5327 = (254106418136066:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5327 = 254106418136066 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5327 = (13327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_332
