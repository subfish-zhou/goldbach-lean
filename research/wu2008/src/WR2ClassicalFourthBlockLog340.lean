import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints340
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_340 (j : Fin 16) (hj : 16*340+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*340+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*340+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5440) ≤ val WuPaper.ClassicalFourthData.Bq 5440
    have hp : val WuPaper.ClassicalFourthData.Bq 5440 = (255554053284977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5440 = 255554053284977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5440 = (84:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5441) ≤ val WuPaper.ClassicalFourthData.Bq 5441
    have hp : val WuPaper.ClassicalFourthData.Bq 5441 = (255566563687372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5441 = 255566563687372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5441 = (13441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5442) ≤ val WuPaper.ClassicalFourthData.Bq 5442
    have hp : val WuPaper.ClassicalFourthData.Bq 5442 = (255579068889811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5442 = 255579068889811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5442 = (6721:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5443) ≤ val WuPaper.ClassicalFourthData.Bq 5443
    have hp : val WuPaper.ClassicalFourthData.Bq 5443 = (255591568894159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5443 = 255591568894159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5443 = (13443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5444) ≤ val WuPaper.ClassicalFourthData.Bq 5444
    have hp : val WuPaper.ClassicalFourthData.Bq 5444 = (255604063702285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5444 = 255604063702285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5444 = (3361:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5445) ≤ val WuPaper.ClassicalFourthData.Bq 5445
    have hp : val WuPaper.ClassicalFourthData.Bq 5445 = (255616553316054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5445 = 255616553316054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5445 = (2689:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5446) ≤ val WuPaper.ClassicalFourthData.Bq 5446
    have hp : val WuPaper.ClassicalFourthData.Bq 5446 = (255629037737331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5446 = 255629037737331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5446 = (6723:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5447) ≤ val WuPaper.ClassicalFourthData.Bq 5447
    have hp : val WuPaper.ClassicalFourthData.Bq 5447 = (255641516967981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5447 = 255641516967981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5447 = (13447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5447
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5448) ≤ val WuPaper.ClassicalFourthData.Bq 5448
    have hp : val WuPaper.ClassicalFourthData.Bq 5448 = (255653991009868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5448 = 255653991009868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5448 = (1681:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5449) ≤ val WuPaper.ClassicalFourthData.Bq 5449
    have hp : val WuPaper.ClassicalFourthData.Bq 5449 = (255666459864853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5449 = 255666459864853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5449 = (13449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5450) ≤ val WuPaper.ClassicalFourthData.Bq 5450
    have hp : val WuPaper.ClassicalFourthData.Bq 5450 = (255678923534800:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5450 = 255678923534800 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5450 = (269:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5451) ≤ val WuPaper.ClassicalFourthData.Bq 5451
    have hp : val WuPaper.ClassicalFourthData.Bq 5451 = (255691382021570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5451 = 255691382021570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5451 = (13451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5452) ≤ val WuPaper.ClassicalFourthData.Bq 5452
    have hp : val WuPaper.ClassicalFourthData.Bq 5452 = (255703835327022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5452 = 255703835327022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5452 = (3363:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5453) ≤ val WuPaper.ClassicalFourthData.Bq 5453
    have hp : val WuPaper.ClassicalFourthData.Bq 5453 = (255716283453017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5453 = 255716283453017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5453 = (13453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5454) ≤ val WuPaper.ClassicalFourthData.Bq 5454
    have hp : val WuPaper.ClassicalFourthData.Bq 5454 = (255728726401415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5454 = 255728726401415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5454 = (6727:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5455) ≤ val WuPaper.ClassicalFourthData.Bq 5455
    have hp : val WuPaper.ClassicalFourthData.Bq 5455 = (255741164174072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5455 = 255741164174072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5455 = (2691:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_340
