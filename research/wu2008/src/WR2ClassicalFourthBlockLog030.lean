import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints030
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_030 (j : Fin 16) (hj : 16*30+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*30+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*30+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 480) ≤ val WuPaper.ClassicalFourthData.Bq 480
    have hp : val WuPaper.ClassicalFourthData.Bq 480 = (53456927031606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 480 = 53456927031606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 480 = (53:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 481) ≤ val WuPaper.ClassicalFourthData.Bq 481
    have hp : val WuPaper.ClassicalFourthData.Bq 481 = (53555889486672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 481 = 53555889486672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 481 = (8481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 482) ≤ val WuPaper.ClassicalFourthData.Bq 482
    have hp : val WuPaper.ClassicalFourthData.Bq 482 = (53654805120889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 482 = 53654805120889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 482 = (4241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 483) ≤ val WuPaper.ClassicalFourthData.Bq 483
    have hp : val WuPaper.ClassicalFourthData.Bq 483 = (53753673961293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 483 = 53753673961293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 483 = (8483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 484) ≤ val WuPaper.ClassicalFourthData.Bq 484
    have hp : val WuPaper.ClassicalFourthData.Bq 484 = (53852496034900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 484 = 53852496034900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 484 = (2121:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 485) ≤ val WuPaper.ClassicalFourthData.Bq 485
    have hp : val WuPaper.ClassicalFourthData.Bq 485 = (53951271368707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 485 = 53951271368707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 485 = (1697:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 486) ≤ val WuPaper.ClassicalFourthData.Bq 486
    have hp : val WuPaper.ClassicalFourthData.Bq 486 = (54049999989690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 486 = 54049999989690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 486 = (4243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 487) ≤ val WuPaper.ClassicalFourthData.Bq 487
    have hp : val WuPaper.ClassicalFourthData.Bq 487 = (54148681924806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 487 = 54148681924806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 487 = (8487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 488) ≤ val WuPaper.ClassicalFourthData.Bq 488
    have hp : val WuPaper.ClassicalFourthData.Bq 488 = (54247317200992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 488 = 54247317200992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 488 = (1061:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 489) ≤ val WuPaper.ClassicalFourthData.Bq 489
    have hp : val WuPaper.ClassicalFourthData.Bq 489 = (54345905845167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 489 = 54345905845167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 489 = (8489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 490) ≤ val WuPaper.ClassicalFourthData.Bq 490
    have hp : val WuPaper.ClassicalFourthData.Bq 490 = (54444447884228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 490 = 54444447884228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 490 = (849:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 491) ≤ val WuPaper.ClassicalFourthData.Bq 491
    have hp : val WuPaper.ClassicalFourthData.Bq 491 = (54542943345053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 491 = 54542943345053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 491 = (8491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 492) ≤ val WuPaper.ClassicalFourthData.Bq 492
    have hp : val WuPaper.ClassicalFourthData.Bq 492 = (54641392254502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 492 = 54641392254502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 492 = (2123:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 493) ≤ val WuPaper.ClassicalFourthData.Bq 493
    have hp : val WuPaper.ClassicalFourthData.Bq 493 = (54739794639413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 493 = 54739794639413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 493 = (8493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 494) ≤ val WuPaper.ClassicalFourthData.Bq 494
    have hp : val WuPaper.ClassicalFourthData.Bq 494 = (54838150526606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 494 = 54838150526606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 494 = (4247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 495) ≤ val WuPaper.ClassicalFourthData.Bq 495
    have hp : val WuPaper.ClassicalFourthData.Bq 495 = (54936459942881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 495 = 54936459942881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 495 = (1699:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_030
