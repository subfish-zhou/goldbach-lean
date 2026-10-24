import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints336
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_336 (j : Fin 16) (hj : 16*336+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*336+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*336+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5376) ≤ val WuPaper.ClassicalFourthData.Bq 5376
    have hp : val WuPaper.ClassicalFourthData.Bq 5376 = (254742485560637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5376 = 254742485560637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5376 = (418:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5377) ≤ val WuPaper.ClassicalFourthData.Bq 5377
    have hp : val WuPaper.ClassicalFourthData.Bq 5377 = (254755332680751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5377 = 254755332680751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5377 = (13377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5378) ≤ val WuPaper.ClassicalFourthData.Bq 5378
    have hp : val WuPaper.ClassicalFourthData.Bq 5378 = (254768174479745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5378 = 254768174479745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5378 = (6689:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5379) ≤ val WuPaper.ClassicalFourthData.Bq 5379
    have hp : val WuPaper.ClassicalFourthData.Bq 5379 = (254781010959538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5379 = 254781010959538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5379 = (13379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5380) ≤ val WuPaper.ClassicalFourthData.Bq 5380
    have hp : val WuPaper.ClassicalFourthData.Bq 5380 = (254793842122047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5380 = 254793842122047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5380 = (669:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5381) ≤ val WuPaper.ClassicalFourthData.Bq 5381
    have hp : val WuPaper.ClassicalFourthData.Bq 5381 = (254806667969188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5381 = 254806667969188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5381 = (13381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5382) ≤ val WuPaper.ClassicalFourthData.Bq 5382
    have hp : val WuPaper.ClassicalFourthData.Bq 5382 = (254819488502878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5382 = 254819488502878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5382 = (6691:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5383) ≤ val WuPaper.ClassicalFourthData.Bq 5383
    have hp : val WuPaper.ClassicalFourthData.Bq 5383 = (254832303725032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5383 = 254832303725032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5383 = (13383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5383
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5384) ≤ val WuPaper.ClassicalFourthData.Bq 5384
    have hp : val WuPaper.ClassicalFourthData.Bq 5384 = (254845113637564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5384 = 254845113637564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5384 = (1673:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5385) ≤ val WuPaper.ClassicalFourthData.Bq 5385
    have hp : val WuPaper.ClassicalFourthData.Bq 5385 = (254857918242386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5385 = 254857918242386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5385 = (2677:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5386) ≤ val WuPaper.ClassicalFourthData.Bq 5386
    have hp : val WuPaper.ClassicalFourthData.Bq 5386 = (254870717541413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5386 = 254870717541413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5386 = (6693:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5387) ≤ val WuPaper.ClassicalFourthData.Bq 5387
    have hp : val WuPaper.ClassicalFourthData.Bq 5387 = (254883511536556:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5387 = 254883511536556 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5387 = (13387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5388) ≤ val WuPaper.ClassicalFourthData.Bq 5388
    have hp : val WuPaper.ClassicalFourthData.Bq 5388 = (254896300229725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5388 = 254896300229725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5388 = (3347:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5389) ≤ val WuPaper.ClassicalFourthData.Bq 5389
    have hp : val WuPaper.ClassicalFourthData.Bq 5389 = (254909083622832:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5389 = 254909083622832 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5389 = (13389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5390) ≤ val WuPaper.ClassicalFourthData.Bq 5390
    have hp : val WuPaper.ClassicalFourthData.Bq 5390 = (254921861717785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5390 = 254921861717785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5390 = (1339:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5391) ≤ val WuPaper.ClassicalFourthData.Bq 5391
    have hp : val WuPaper.ClassicalFourthData.Bq 5391 = (254934634516493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5391 = 254934634516493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5391 = (13391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5391
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_336
