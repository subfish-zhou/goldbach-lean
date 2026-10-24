import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints027
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_027 (j : Fin 16) (hj : 16*27+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*27+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*27+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 432) ≤ val WuPaper.ClassicalFourthData.Bq 432
    have hp : val WuPaper.ClassicalFourthData.Bq 432 = (48651132981543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 432 = 48651132981543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 432 = (527:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 433) ≤ val WuPaper.ClassicalFourthData.Bq 433
    have hp : val WuPaper.ClassicalFourthData.Bq 433 = (48752375023373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 433 = 48752375023373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 433 = (8433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 434) ≤ val WuPaper.ClassicalFourthData.Bq 434
    have hp : val WuPaper.ClassicalFourthData.Bq 434 = (48853568923040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 434 = 48853568923040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 434 = (4217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 435) ≤ val WuPaper.ClassicalFourthData.Bq 435
    have hp : val WuPaper.ClassicalFourthData.Bq 435 = (48954714708549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 435 = 48954714708549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 435 = (1687:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 436) ≤ val WuPaper.ClassicalFourthData.Bq 436
    have hp : val WuPaper.ClassicalFourthData.Bq 436 = (49055812407886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 436 = 49055812407886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 436 = (2109:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 437) ≤ val WuPaper.ClassicalFourthData.Bq 437
    have hp : val WuPaper.ClassicalFourthData.Bq 437 = (49156862049014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 437 = 49156862049014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 437 = (8437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 438) ≤ val WuPaper.ClassicalFourthData.Bq 438
    have hp : val WuPaper.ClassicalFourthData.Bq 438 = (49257863659878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 438 = 49257863659878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 438 = (4219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 439) ≤ val WuPaper.ClassicalFourthData.Bq 439
    have hp : val WuPaper.ClassicalFourthData.Bq 439 = (49358817268401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 439 = 49358817268401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 439 = (8439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 440) ≤ val WuPaper.ClassicalFourthData.Bq 440
    have hp : val WuPaper.ClassicalFourthData.Bq 440 = (49459722902485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 440 = 49459722902485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 440 = (211:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 441) ≤ val WuPaper.ClassicalFourthData.Bq 441
    have hp : val WuPaper.ClassicalFourthData.Bq 441 = (49560580590013:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 441 = 49560580590013 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 441 = (8441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 442) ≤ val WuPaper.ClassicalFourthData.Bq 442
    have hp : val WuPaper.ClassicalFourthData.Bq 442 = (49661390358847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 442 = 49661390358847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 442 = (4221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 443) ≤ val WuPaper.ClassicalFourthData.Bq 443
    have hp : val WuPaper.ClassicalFourthData.Bq 443 = (49762152236827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 443 = 49762152236827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 443 = (8443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 444) ≤ val WuPaper.ClassicalFourthData.Bq 444
    have hp : val WuPaper.ClassicalFourthData.Bq 444 = (49862866251774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 444 = 49862866251774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 444 = (2111:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 445) ≤ val WuPaper.ClassicalFourthData.Bq 445
    have hp : val WuPaper.ClassicalFourthData.Bq 445 = (49963532431488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 445 = 49963532431488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 445 = (1689:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 446) ≤ val WuPaper.ClassicalFourthData.Bq 446
    have hp : val WuPaper.ClassicalFourthData.Bq 446 = (50064150803749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 446 = 50064150803749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 446 = (4223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 447) ≤ val WuPaper.ClassicalFourthData.Bq 447
    have hp : val WuPaper.ClassicalFourthData.Bq 447 = (50164721396316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 447 = 50164721396316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 447 = (8447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_027
