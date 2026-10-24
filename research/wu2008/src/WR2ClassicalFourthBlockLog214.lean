import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints214
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_214 (j : Fin 16) (hj : 16*214+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*214+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*214+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3424) ≤ val WuPaper.ClassicalFourthData.Bq 3424
    have hp : val WuPaper.ClassicalFourthData.Bq 3424 = (216534885981796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3424 = 216534885981796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3424 = (357:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3425) ≤ val WuPaper.ClassicalFourthData.Bq 3425
    have hp : val WuPaper.ClassicalFourthData.Bq 3425 = (216563089214485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3425 = 216563089214485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3425 = (457:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3426) ≤ val WuPaper.ClassicalFourthData.Bq 3426
    have hp : val WuPaper.ClassicalFourthData.Bq 3426 = (216591281160511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3426 = 216591281160511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3426 = (5713:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3427) ≤ val WuPaper.ClassicalFourthData.Bq 3427
    have hp : val WuPaper.ClassicalFourthData.Bq 3427 = (216619461824545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3427 = 216619461824545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3427 = (11427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3428) ≤ val WuPaper.ClassicalFourthData.Bq 3428
    have hp : val WuPaper.ClassicalFourthData.Bq 3428 = (216647631211260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3428 = 216647631211260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3428 = (2857:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3429) ≤ val WuPaper.ClassicalFourthData.Bq 3429
    have hp : val WuPaper.ClassicalFourthData.Bq 3429 = (216675789325323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3429 = 216675789325323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3429 = (11429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3430) ≤ val WuPaper.ClassicalFourthData.Bq 3430
    have hp : val WuPaper.ClassicalFourthData.Bq 3430 = (216703936171401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3430 = 216703936171401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3430 = (1143:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3431) ≤ val WuPaper.ClassicalFourthData.Bq 3431
    have hp : val WuPaper.ClassicalFourthData.Bq 3431 = (216732071754157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3431 = 216732071754157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3431 = (11431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3431
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3432) ≤ val WuPaper.ClassicalFourthData.Bq 3432
    have hp : val WuPaper.ClassicalFourthData.Bq 3432 = (216760196078253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3432 = 216760196078253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3432 = (1429:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3433) ≤ val WuPaper.ClassicalFourthData.Bq 3433
    have hp : val WuPaper.ClassicalFourthData.Bq 3433 = (216788309148349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3433 = 216788309148349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3433 = (11433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3434) ≤ val WuPaper.ClassicalFourthData.Bq 3434
    have hp : val WuPaper.ClassicalFourthData.Bq 3434 = (216816410969100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3434 = 216816410969100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3434 = (5717:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3435) ≤ val WuPaper.ClassicalFourthData.Bq 3435
    have hp : val WuPaper.ClassicalFourthData.Bq 3435 = (216844501545161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3435 = 216844501545161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3435 = (2287:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3436) ≤ val WuPaper.ClassicalFourthData.Bq 3436
    have hp : val WuPaper.ClassicalFourthData.Bq 3436 = (216872580881185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3436 = 216872580881185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3436 = (2859:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3437) ≤ val WuPaper.ClassicalFourthData.Bq 3437
    have hp : val WuPaper.ClassicalFourthData.Bq 3437 = (216900648981822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3437 = 216900648981822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3437 = (11437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3438) ≤ val WuPaper.ClassicalFourthData.Bq 3438
    have hp : val WuPaper.ClassicalFourthData.Bq 3438 = (216928705851719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3438 = 216928705851719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3438 = (5719:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3439) ≤ val WuPaper.ClassicalFourthData.Bq 3439
    have hp : val WuPaper.ClassicalFourthData.Bq 3439 = (216956751495521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3439 = 216956751495521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3439 = (11439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_214
