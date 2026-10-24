import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints339
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_339 (j : Fin 16) (hj : 16*339+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*339+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*339+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5424) ≤ val WuPaper.ClassicalFourthData.Bq 5424
    have hp : val WuPaper.ClassicalFourthData.Bq 5424 = (255353178125550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5424 = 255353178125550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5424 = (839:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5425) ≤ val WuPaper.ClassicalFourthData.Bq 5425
    have hp : val WuPaper.ClassicalFourthData.Bq 5425 = (255365771981881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5425 = 255365771981881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5425 = (537:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5426) ≤ val WuPaper.ClassicalFourthData.Bq 5426
    have hp : val WuPaper.ClassicalFourthData.Bq 5426 = (255378360608268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5426 = 255378360608268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5426 = (6713:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5427) ≤ val WuPaper.ClassicalFourthData.Bq 5427
    have hp : val WuPaper.ClassicalFourthData.Bq 5427 = (255390944006592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5427 = 255390944006592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5427 = (13427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5428) ≤ val WuPaper.ClassicalFourthData.Bq 5428
    have hp : val WuPaper.ClassicalFourthData.Bq 5428 = (255403522178730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5428 = 255403522178730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5428 = (3357:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5429) ≤ val WuPaper.ClassicalFourthData.Bq 5429
    have hp : val WuPaper.ClassicalFourthData.Bq 5429 = (255416095126563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5429 = 255416095126563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5429 = (13429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5430) ≤ val WuPaper.ClassicalFourthData.Bq 5430
    have hp : val WuPaper.ClassicalFourthData.Bq 5430 = (255428662851967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5430 = 255428662851967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5430 = (1343:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5431) ≤ val WuPaper.ClassicalFourthData.Bq 5431
    have hp : val WuPaper.ClassicalFourthData.Bq 5431 = (255441225356820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5431 = 255441225356820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5431 = (13431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5431
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5432) ≤ val WuPaper.ClassicalFourthData.Bq 5432
    have hp : val WuPaper.ClassicalFourthData.Bq 5432 = (255453782642997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5432 = 255453782642997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5432 = (1679:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5433) ≤ val WuPaper.ClassicalFourthData.Bq 5433
    have hp : val WuPaper.ClassicalFourthData.Bq 5433 = (255466334712374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5433 = 255466334712374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5433 = (13433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5434) ≤ val WuPaper.ClassicalFourthData.Bq 5434
    have hp : val WuPaper.ClassicalFourthData.Bq 5434 = (255478881566826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5434 = 255478881566826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5434 = (6717:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5435) ≤ val WuPaper.ClassicalFourthData.Bq 5435
    have hp : val WuPaper.ClassicalFourthData.Bq 5435 = (255491423208225:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5435 = 255491423208225 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5435 = (2687:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5436) ≤ val WuPaper.ClassicalFourthData.Bq 5436
    have hp : val WuPaper.ClassicalFourthData.Bq 5436 = (255503959638447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5436 = 255503959638447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5436 = (3359:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5437) ≤ val WuPaper.ClassicalFourthData.Bq 5437
    have hp : val WuPaper.ClassicalFourthData.Bq 5437 = (255516490859361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5437 = 255516490859361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5437 = (13437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5438) ≤ val WuPaper.ClassicalFourthData.Bq 5438
    have hp : val WuPaper.ClassicalFourthData.Bq 5438 = (255529016872841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5438 = 255529016872841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5438 = (6719:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5439) ≤ val WuPaper.ClassicalFourthData.Bq 5439
    have hp : val WuPaper.ClassicalFourthData.Bq 5439 = (255541537680756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5439 = 255541537680756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5439 = (13439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_339
