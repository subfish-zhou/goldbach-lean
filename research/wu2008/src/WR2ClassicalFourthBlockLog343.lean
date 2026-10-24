import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints343
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_343 (j : Fin 16) (hj : 16*343+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*343+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*343+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5488) ≤ val WuPaper.ClassicalFourthData.Bq 5488
    have hp : val WuPaper.ClassicalFourthData.Bq 5488 = (256148719197949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5488 = 256148719197949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5488 = (843:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5489) ≤ val WuPaper.ClassicalFourthData.Bq 5489
    have hp : val WuPaper.ClassicalFourthData.Bq 5489 = (256160982095555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5489 = 256160982095555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5489 = (13489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5490) ≤ val WuPaper.ClassicalFourthData.Bq 5490
    have hp : val WuPaper.ClassicalFourthData.Bq 5490 = (256173239881972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5490 = 256173239881972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5490 = (1349:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5491) ≤ val WuPaper.ClassicalFourthData.Bq 5491
    have hp : val WuPaper.ClassicalFourthData.Bq 5491 = (256185492559030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5491 = 256185492559030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5491 = (13491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5492) ≤ val WuPaper.ClassicalFourthData.Bq 5492
    have hp : val WuPaper.ClassicalFourthData.Bq 5492 = (256197740128560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5492 = 256197740128560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5492 = (3373:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5493) ≤ val WuPaper.ClassicalFourthData.Bq 5493
    have hp : val WuPaper.ClassicalFourthData.Bq 5493 = (256209982592389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5493 = 256209982592389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5493 = (13493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5494) ≤ val WuPaper.ClassicalFourthData.Bq 5494
    have hp : val WuPaper.ClassicalFourthData.Bq 5494 = (256222219952346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5494 = 256222219952346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5494 = (6747:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5495) ≤ val WuPaper.ClassicalFourthData.Bq 5495
    have hp : val WuPaper.ClassicalFourthData.Bq 5495 = (256234452210260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5495 = 256234452210260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5495 = (2699:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5495
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5496) ≤ val WuPaper.ClassicalFourthData.Bq 5496
    have hp : val WuPaper.ClassicalFourthData.Bq 5496 = (256246679367955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5496 = 256246679367955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5496 = (1687:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5497) ≤ val WuPaper.ClassicalFourthData.Bq 5497
    have hp : val WuPaper.ClassicalFourthData.Bq 5497 = (256258901427259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5497 = 256258901427259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5497 = (13497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5498) ≤ val WuPaper.ClassicalFourthData.Bq 5498
    have hp : val WuPaper.ClassicalFourthData.Bq 5498 = (256271118389997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5498 = 256271118389997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5498 = (6749:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5499) ≤ val WuPaper.ClassicalFourthData.Bq 5499
    have hp : val WuPaper.ClassicalFourthData.Bq 5499 = (256283330257992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5499 = 256283330257992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5499 = (13499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5500) ≤ val WuPaper.ClassicalFourthData.Bq 5500
    have hp : val WuPaper.ClassicalFourthData.Bq 5500 = (256295537033069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5500 = 256295537033069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5500 = (27:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5501) ≤ val WuPaper.ClassicalFourthData.Bq 5501
    have hp : val WuPaper.ClassicalFourthData.Bq 5501 = (256307738717051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5501 = 256307738717051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5501 = (13501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5502) ≤ val WuPaper.ClassicalFourthData.Bq 5502
    have hp : val WuPaper.ClassicalFourthData.Bq 5502 = (256319935311759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5502 = 256319935311759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5502 = (6751:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5503) ≤ val WuPaper.ClassicalFourthData.Bq 5503
    have hp : val WuPaper.ClassicalFourthData.Bq 5503 = (256332126819016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5503 = 256332126819016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5503 = (13503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_343
