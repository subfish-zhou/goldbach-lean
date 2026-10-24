import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints530
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_530 (j : Fin 16) (hj : 16*530+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*530+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*530+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8480) ≤ val WuPaper.ClassicalFourthData.Bq 8480
    have hp : val WuPaper.ClassicalFourthData.Bq 8480 = (276173058696149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8480 = 276173058696149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8480 = (103:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8481) ≤ val WuPaper.ClassicalFourthData.Bq 8481
    have hp : val WuPaper.ClassicalFourthData.Bq 8481 = (276175748273328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8481 = 276175748273328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8481 = (16481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8482) ≤ val WuPaper.ClassicalFourthData.Bq 8482
    have hp : val WuPaper.ClassicalFourthData.Bq 8482 = (276178435966200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8482 = 276178435966200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8482 = (8241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8483) ≤ val WuPaper.ClassicalFourthData.Bq 8483
    have hp : val WuPaper.ClassicalFourthData.Bq 8483 = (276181121775357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8483 = 276181121775357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8483 = (16483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8484) ≤ val WuPaper.ClassicalFourthData.Bq 8484
    have hp : val WuPaper.ClassicalFourthData.Bq 8484 = (276183805701392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8484 = 276183805701392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8484 = (4121:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8485) ≤ val WuPaper.ClassicalFourthData.Bq 8485
    have hp : val WuPaper.ClassicalFourthData.Bq 8485 = (276186487744896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8485 = 276186487744896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8485 = (3297:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8486) ≤ val WuPaper.ClassicalFourthData.Bq 8486
    have hp : val WuPaper.ClassicalFourthData.Bq 8486 = (276189167906462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8486 = 276189167906462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8486 = (8243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8487) ≤ val WuPaper.ClassicalFourthData.Bq 8487
    have hp : val WuPaper.ClassicalFourthData.Bq 8487 = (276191846186681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8487 = 276191846186681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8487 = (16487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8488) ≤ val WuPaper.ClassicalFourthData.Bq 8488
    have hp : val WuPaper.ClassicalFourthData.Bq 8488 = (276194522586144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8488 = 276194522586144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8488 = (2061:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8489) ≤ val WuPaper.ClassicalFourthData.Bq 8489
    have hp : val WuPaper.ClassicalFourthData.Bq 8489 = (276197197105444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8489 = 276197197105444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8489 = (16489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8490) ≤ val WuPaper.ClassicalFourthData.Bq 8490
    have hp : val WuPaper.ClassicalFourthData.Bq 8490 = (276199869745171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8490 = 276199869745171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8490 = (1649:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8491) ≤ val WuPaper.ClassicalFourthData.Bq 8491
    have hp : val WuPaper.ClassicalFourthData.Bq 8491 = (276202540505917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8491 = 276202540505917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8491 = (16491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8492) ≤ val WuPaper.ClassicalFourthData.Bq 8492
    have hp : val WuPaper.ClassicalFourthData.Bq 8492 = (276205209388271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8492 = 276205209388271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8492 = (4123:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8493) ≤ val WuPaper.ClassicalFourthData.Bq 8493
    have hp : val WuPaper.ClassicalFourthData.Bq 8493 = (276207876392825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8493 = 276207876392825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8493 = (16493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8494) ≤ val WuPaper.ClassicalFourthData.Bq 8494
    have hp : val WuPaper.ClassicalFourthData.Bq 8494 = (276210541520169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8494 = 276210541520169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8494 = (8247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8495) ≤ val WuPaper.ClassicalFourthData.Bq 8495
    have hp : val WuPaper.ClassicalFourthData.Bq 8495 = (276213204770892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8495 = 276213204770892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8495 = (3299:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_530
