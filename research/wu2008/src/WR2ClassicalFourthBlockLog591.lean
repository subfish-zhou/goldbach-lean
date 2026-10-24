import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints591
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_591 (j : Fin 16) (hj : 16*591+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*591+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*591+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9456) ≤ val WuPaper.ClassicalFourthData.Bq 9456
    have hp : val WuPaper.ClassicalFourthData.Bq 9456 = (277985962912498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9456 = 277985962912498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9456 = (1091:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9457) ≤ val WuPaper.ClassicalFourthData.Bq 9457
    have hp : val WuPaper.ClassicalFourthData.Bq 9457 = (277987066661860:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9457 = 277987066661860 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9457 = (17457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9458) ≤ val WuPaper.ClassicalFourthData.Bq 9458
    have hp : val WuPaper.ClassicalFourthData.Bq 9458 = (277988169019546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9458 = 277988169019546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9458 = (8729:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9459) ≤ val WuPaper.ClassicalFourthData.Bq 9459
    have hp : val WuPaper.ClassicalFourthData.Bq 9459 = (277989269985985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9459 = 277989269985985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9459 = (17459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9460) ≤ val WuPaper.ClassicalFourthData.Bq 9460
    have hp : val WuPaper.ClassicalFourthData.Bq 9460 = (277990369561603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9460 = 277990369561603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9460 = (873:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9461) ≤ val WuPaper.ClassicalFourthData.Bq 9461
    have hp : val WuPaper.ClassicalFourthData.Bq 9461 = (277991467746828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9461 = 277991467746828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9461 = (17461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9462) ≤ val WuPaper.ClassicalFourthData.Bq 9462
    have hp : val WuPaper.ClassicalFourthData.Bq 9462 = (277992564542085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9462 = 277992564542085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9462 = (8731:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9463) ≤ val WuPaper.ClassicalFourthData.Bq 9463
    have hp : val WuPaper.ClassicalFourthData.Bq 9463 = (277993659947802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9463 = 277993659947802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9463 = (17463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9463
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9464) ≤ val WuPaper.ClassicalFourthData.Bq 9464
    have hp : val WuPaper.ClassicalFourthData.Bq 9464 = (277994753964405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9464 = 277994753964405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9464 = (2183:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9465) ≤ val WuPaper.ClassicalFourthData.Bq 9465
    have hp : val WuPaper.ClassicalFourthData.Bq 9465 = (277995846592319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9465 = 277995846592319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9465 = (3493:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9466) ≤ val WuPaper.ClassicalFourthData.Bq 9466
    have hp : val WuPaper.ClassicalFourthData.Bq 9466 = (277996937831973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9466 = 277996937831973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9466 = (8733:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9467) ≤ val WuPaper.ClassicalFourthData.Bq 9467
    have hp : val WuPaper.ClassicalFourthData.Bq 9467 = (277998027683790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9467 = 277998027683790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9467 = (17467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9468) ≤ val WuPaper.ClassicalFourthData.Bq 9468
    have hp : val WuPaper.ClassicalFourthData.Bq 9468 = (277999116148199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9468 = 277999116148199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9468 = (4367:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9469) ≤ val WuPaper.ClassicalFourthData.Bq 9469
    have hp : val WuPaper.ClassicalFourthData.Bq 9469 = (278000203225623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9469 = 278000203225623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9469 = (17469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9470) ≤ val WuPaper.ClassicalFourthData.Bq 9470
    have hp : val WuPaper.ClassicalFourthData.Bq 9470 = (278001288916488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9470 = 278001288916488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9470 = (1747:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9471) ≤ val WuPaper.ClassicalFourthData.Bq 9471
    have hp : val WuPaper.ClassicalFourthData.Bq 9471 = (278002373221221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9471 = 278002373221221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9471 = (17471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_591
