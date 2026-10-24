import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints464
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_464 (j : Fin 16) (hj : 16*464+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*464+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*464+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7424) ≤ val WuPaper.ClassicalFourthData.Bq 7424
    have hp : val WuPaper.ClassicalFourthData.Bq 7424 = (272153019833520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7424 = 272153019833520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7424 = (482:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7424
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7425) ≤ val WuPaper.ClassicalFourthData.Bq 7425
    have hp : val WuPaper.ClassicalFourthData.Bq 7425 = (272158074725730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7425 = 272158074725730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7425 = (617:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7425
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7426) ≤ val WuPaper.ClassicalFourthData.Bq 7426
    have hp : val WuPaper.ClassicalFourthData.Bq 7426 = (272163126976040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7426 = 272163126976040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7426 = (7713:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7426
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7427) ≤ val WuPaper.ClassicalFourthData.Bq 7427
    have hp : val WuPaper.ClassicalFourthData.Bq 7427 = (272168176585313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7427 = 272168176585313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7427 = (15427:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7427
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7428) ≤ val WuPaper.ClassicalFourthData.Bq 7428
    have hp : val WuPaper.ClassicalFourthData.Bq 7428 = (272173223554410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7428 = 272173223554410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7428 = (3857:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7428
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7429) ≤ val WuPaper.ClassicalFourthData.Bq 7429
    have hp : val WuPaper.ClassicalFourthData.Bq 7429 = (272178267884191:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7429 = 272178267884191 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7429 = (15429:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7429
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7430) ≤ val WuPaper.ClassicalFourthData.Bq 7430
    have hp : val WuPaper.ClassicalFourthData.Bq 7430 = (272183309575516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7430 = 272183309575516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7430 = (1543:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7430
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7431) ≤ val WuPaper.ClassicalFourthData.Bq 7431
    have hp : val WuPaper.ClassicalFourthData.Bq 7431 = (272188348629247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7431 = 272188348629247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7431 = (15431:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7431
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7432) ≤ val WuPaper.ClassicalFourthData.Bq 7432
    have hp : val WuPaper.ClassicalFourthData.Bq 7432 = (272193385046243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7432 = 272193385046243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7432 = (1929:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7433) ≤ val WuPaper.ClassicalFourthData.Bq 7433
    have hp : val WuPaper.ClassicalFourthData.Bq 7433 = (272198418827363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7433 = 272198418827363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7433 = (15433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7434) ≤ val WuPaper.ClassicalFourthData.Bq 7434
    have hp : val WuPaper.ClassicalFourthData.Bq 7434 = (272203449973467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7434 = 272203449973467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7434 = (7717:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7435) ≤ val WuPaper.ClassicalFourthData.Bq 7435
    have hp : val WuPaper.ClassicalFourthData.Bq 7435 = (272208478485413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7435 = 272208478485413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7435 = (3087:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7436) ≤ val WuPaper.ClassicalFourthData.Bq 7436
    have hp : val WuPaper.ClassicalFourthData.Bq 7436 = (272213504364061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7436 = 272213504364061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7436 = (3859:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7437) ≤ val WuPaper.ClassicalFourthData.Bq 7437
    have hp : val WuPaper.ClassicalFourthData.Bq 7437 = (272218527610268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7437 = 272218527610268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7437 = (15437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7438) ≤ val WuPaper.ClassicalFourthData.Bq 7438
    have hp : val WuPaper.ClassicalFourthData.Bq 7438 = (272223548224893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7438 = 272223548224893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7438 = (7719:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7439) ≤ val WuPaper.ClassicalFourthData.Bq 7439
    have hp : val WuPaper.ClassicalFourthData.Bq 7439 = (272228566208793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7439 = 272228566208793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7439 = (15439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7439
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_464
