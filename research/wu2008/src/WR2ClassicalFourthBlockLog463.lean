import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints463
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_463 (j : Fin 16) (hj : 16*463+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*463+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*463+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7408) ≤ val WuPaper.ClassicalFourthData.Bq 7408
    have hp : val WuPaper.ClassicalFourthData.Bq 7408 = (272071781555748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7408 = 272071781555748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7408 = (963:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7409) ≤ val WuPaper.ClassicalFourthData.Bq 7409
    have hp : val WuPaper.ClassicalFourthData.Bq 7409 = (272076878835754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7409 = 272076878835754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7409 = (15409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7410) ≤ val WuPaper.ClassicalFourthData.Bq 7410
    have hp : val WuPaper.ClassicalFourthData.Bq 7410 = (272081973460036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7410 = 272081973460036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7410 = (1541:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7411) ≤ val WuPaper.ClassicalFourthData.Bq 7411
    have hp : val WuPaper.ClassicalFourthData.Bq 7411 = (272087065429459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7411 = 272087065429459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7411 = (15411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7412) ≤ val WuPaper.ClassicalFourthData.Bq 7412
    have hp : val WuPaper.ClassicalFourthData.Bq 7412 = (272092154744890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7412 = 272092154744890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7412 = (3853:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7413) ≤ val WuPaper.ClassicalFourthData.Bq 7413
    have hp : val WuPaper.ClassicalFourthData.Bq 7413 = (272097241407194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7413 = 272097241407194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7413 = (15413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7414) ≤ val WuPaper.ClassicalFourthData.Bq 7414
    have hp : val WuPaper.ClassicalFourthData.Bq 7414 = (272102325417238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7414 = 272102325417238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7414 = (7707:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7415) ≤ val WuPaper.ClassicalFourthData.Bq 7415
    have hp : val WuPaper.ClassicalFourthData.Bq 7415 = (272107406775886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7415 = 272107406775886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7415 = (3083:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7415
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7416) ≤ val WuPaper.ClassicalFourthData.Bq 7416
    have hp : val WuPaper.ClassicalFourthData.Bq 7416 = (272112485484003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7416 = 272112485484003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7416 = (1927:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7417) ≤ val WuPaper.ClassicalFourthData.Bq 7417
    have hp : val WuPaper.ClassicalFourthData.Bq 7417 = (272117561542454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7417 = 272117561542454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7417 = (15417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7418) ≤ val WuPaper.ClassicalFourthData.Bq 7418
    have hp : val WuPaper.ClassicalFourthData.Bq 7418 = (272122634952104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7418 = 272122634952104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7418 = (7709:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7419) ≤ val WuPaper.ClassicalFourthData.Bq 7419
    have hp : val WuPaper.ClassicalFourthData.Bq 7419 = (272127705713815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7419 = 272127705713815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7419 = (15419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7420) ≤ val WuPaper.ClassicalFourthData.Bq 7420
    have hp : val WuPaper.ClassicalFourthData.Bq 7420 = (272132773828452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7420 = 272132773828452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7420 = (771:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7421) ≤ val WuPaper.ClassicalFourthData.Bq 7421
    have hp : val WuPaper.ClassicalFourthData.Bq 7421 = (272137839296878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7421 = 272137839296878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7421 = (15421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7422) ≤ val WuPaper.ClassicalFourthData.Bq 7422
    have hp : val WuPaper.ClassicalFourthData.Bq 7422 = (272142902119957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7422 = 272142902119957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7422 = (7711:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7423) ≤ val WuPaper.ClassicalFourthData.Bq 7423
    have hp : val WuPaper.ClassicalFourthData.Bq 7423 = (272147962298550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7423 = 272147962298550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7423 = (15423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_463
