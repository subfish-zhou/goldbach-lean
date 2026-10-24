import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints276
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_276 (j : Fin 16) (hj : 16*276+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*276+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*276+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4416) ≤ val WuPaper.ClassicalFourthData.Bq 4416
    have hp : val WuPaper.ClassicalFourthData.Bq 4416 = (239639270256271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4416 = 239639270256271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4416 = (388:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4417) ≤ val WuPaper.ClassicalFourthData.Bq 4417
    have hp : val WuPaper.ClassicalFourthData.Bq 4417 = (239658245666280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4417 = 239658245666280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4417 = (12417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4418) ≤ val WuPaper.ClassicalFourthData.Bq 4418
    have hp : val WuPaper.ClassicalFourthData.Bq 4418 = (239677213473503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4418 = 239677213473503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4418 = (6209:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4419) ≤ val WuPaper.ClassicalFourthData.Bq 4419
    have hp : val WuPaper.ClassicalFourthData.Bq 4419 = (239696173680856:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4419 = 239696173680856 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4419 = (12419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4420) ≤ val WuPaper.ClassicalFourthData.Bq 4420
    have hp : val WuPaper.ClassicalFourthData.Bq 4420 = (239715126291255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4420 = 239715126291255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4420 = (621:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4421) ≤ val WuPaper.ClassicalFourthData.Bq 4421
    have hp : val WuPaper.ClassicalFourthData.Bq 4421 = (239734071307613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4421 = 239734071307613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4421 = (12421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4422) ≤ val WuPaper.ClassicalFourthData.Bq 4422
    have hp : val WuPaper.ClassicalFourthData.Bq 4422 = (239753008732844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4422 = 239753008732844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4422 = (6211:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4423) ≤ val WuPaper.ClassicalFourthData.Bq 4423
    have hp : val WuPaper.ClassicalFourthData.Bq 4423 = (239771938569858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4423 = 239771938569858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4423 = (12423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4423
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4424) ≤ val WuPaper.ClassicalFourthData.Bq 4424
    have hp : val WuPaper.ClassicalFourthData.Bq 4424 = (239790860821566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4424 = 239790860821566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4424 = (1553:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4425) ≤ val WuPaper.ClassicalFourthData.Bq 4425
    have hp : val WuPaper.ClassicalFourthData.Bq 4425 = (239809775490877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4425 = 239809775490877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4425 = (497:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4426) ≤ val WuPaper.ClassicalFourthData.Bq 4426
    have hp : val WuPaper.ClassicalFourthData.Bq 4426 = (239828682580697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4426 = 239828682580697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4426 = (6213:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4427) ≤ val WuPaper.ClassicalFourthData.Bq 4427
    have hp : val WuPaper.ClassicalFourthData.Bq 4427 = (239847582093933:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4427 = 239847582093933 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4427 = (12427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4428) ≤ val WuPaper.ClassicalFourthData.Bq 4428
    have hp : val WuPaper.ClassicalFourthData.Bq 4428 = (239866474033490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4428 = 239866474033490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4428 = (3107:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4429) ≤ val WuPaper.ClassicalFourthData.Bq 4429
    have hp : val WuPaper.ClassicalFourthData.Bq 4429 = (239885358402271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4429 = 239885358402271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4429 = (12429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4430) ≤ val WuPaper.ClassicalFourthData.Bq 4430
    have hp : val WuPaper.ClassicalFourthData.Bq 4430 = (239904235203178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4430 = 239904235203178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4430 = (1243:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4431) ≤ val WuPaper.ClassicalFourthData.Bq 4431
    have hp : val WuPaper.ClassicalFourthData.Bq 4431 = (239923104439112:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4431 = 239923104439112 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4431 = (12431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4431
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_276
