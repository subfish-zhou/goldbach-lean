import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints212
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_212 (j : Fin 16) (hj : 16*212+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*212+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*212+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3392) ≤ val WuPaper.ClassicalFourthData.Bq 3392
    have hp : val WuPaper.ClassicalFourthData.Bq 3392 = (215626395091114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3392 = 215626395091114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3392 = (356:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3393) ≤ val WuPaper.ClassicalFourthData.Bq 3393
    have hp : val WuPaper.ClassicalFourthData.Bq 3393 = (215654961978434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3393 = 215654961978434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3393 = (11393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3394) ≤ val WuPaper.ClassicalFourthData.Bq 3394
    have hp : val WuPaper.ClassicalFourthData.Bq 3394 = (215683517428313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3394 = 215683517428313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3394 = (5697:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3395) ≤ val WuPaper.ClassicalFourthData.Bq 3395
    have hp : val WuPaper.ClassicalFourthData.Bq 3395 = (215712061445502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3395 = 215712061445502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3395 = (2279:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3396) ≤ val WuPaper.ClassicalFourthData.Bq 3396
    have hp : val WuPaper.ClassicalFourthData.Bq 3396 = (215740594034745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3396 = 215740594034745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3396 = (2849:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3397) ≤ val WuPaper.ClassicalFourthData.Bq 3397
    have hp : val WuPaper.ClassicalFourthData.Bq 3397 = (215769115200787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3397 = 215769115200787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3397 = (11397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3398) ≤ val WuPaper.ClassicalFourthData.Bq 3398
    have hp : val WuPaper.ClassicalFourthData.Bq 3398 = (215797624948367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3398 = 215797624948367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3398 = (5699:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3399) ≤ val WuPaper.ClassicalFourthData.Bq 3399
    have hp : val WuPaper.ClassicalFourthData.Bq 3399 = (215826123282226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3399 = 215826123282226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3399 = (11399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3399
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3400) ≤ val WuPaper.ClassicalFourthData.Bq 3400
    have hp : val WuPaper.ClassicalFourthData.Bq 3400 = (215854610207100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3400 = 215854610207100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3400 = (57:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3401) ≤ val WuPaper.ClassicalFourthData.Bq 3401
    have hp : val WuPaper.ClassicalFourthData.Bq 3401 = (215883085727722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3401 = 215883085727722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3401 = (11401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3402) ≤ val WuPaper.ClassicalFourthData.Bq 3402
    have hp : val WuPaper.ClassicalFourthData.Bq 3402 = (215911549848825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3402 = 215911549848825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3402 = (5701:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3403) ≤ val WuPaper.ClassicalFourthData.Bq 3403
    have hp : val WuPaper.ClassicalFourthData.Bq 3403 = (215940002575137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3403 = 215940002575137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3403 = (11403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3404) ≤ val WuPaper.ClassicalFourthData.Bq 3404
    have hp : val WuPaper.ClassicalFourthData.Bq 3404 = (215968443911386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3404 = 215968443911386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3404 = (2851:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3405) ≤ val WuPaper.ClassicalFourthData.Bq 3405
    have hp : val WuPaper.ClassicalFourthData.Bq 3405 = (215996873862297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3405 = 215996873862297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3405 = (2281:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3406) ≤ val WuPaper.ClassicalFourthData.Bq 3406
    have hp : val WuPaper.ClassicalFourthData.Bq 3406 = (216025292432590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3406 = 216025292432590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3406 = (5703:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3407) ≤ val WuPaper.ClassicalFourthData.Bq 3407
    have hp : val WuPaper.ClassicalFourthData.Bq 3407 = (216053699626988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3407 = 216053699626988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3407 = (11407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_212
