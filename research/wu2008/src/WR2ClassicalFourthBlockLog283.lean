import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints283
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_283 (j : Fin 16) (hj : 16*283+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*283+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*283+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4528) ≤ val WuPaper.ClassicalFourthData.Bq 4528
    have hp : val WuPaper.ClassicalFourthData.Bq 4528 = (241717913890038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4528 = 241717913890038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4528 = (783:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4529) ≤ val WuPaper.ClassicalFourthData.Bq 4529
    have hp : val WuPaper.ClassicalFourthData.Bq 4529 = (241736055620427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4529 = 241736055620427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4529 = (12529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4530) ≤ val WuPaper.ClassicalFourthData.Bq 4530
    have hp : val WuPaper.ClassicalFourthData.Bq 4530 = (241754190066624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4530 = 241754190066624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4530 = (1253:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4531) ≤ val WuPaper.ClassicalFourthData.Bq 4531
    have hp : val WuPaper.ClassicalFourthData.Bq 4531 = (241772317231400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4531 = 241772317231400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4531 = (12531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4532) ≤ val WuPaper.ClassicalFourthData.Bq 4532
    have hp : val WuPaper.ClassicalFourthData.Bq 4532 = (241790437117528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4532 = 241790437117528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4532 = (3133:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4533) ≤ val WuPaper.ClassicalFourthData.Bq 4533
    have hp : val WuPaper.ClassicalFourthData.Bq 4533 = (241808549727777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4533 = 241808549727777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4533 = (12533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4534) ≤ val WuPaper.ClassicalFourthData.Bq 4534
    have hp : val WuPaper.ClassicalFourthData.Bq 4534 = (241826655064918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4534 = 241826655064918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4534 = (6267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4535) ≤ val WuPaper.ClassicalFourthData.Bq 4535
    have hp : val WuPaper.ClassicalFourthData.Bq 4535 = (241844753131716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4535 = 241844753131716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4535 = (2507:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4536) ≤ val WuPaper.ClassicalFourthData.Bq 4536
    have hp : val WuPaper.ClassicalFourthData.Bq 4536 = (241862843930939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4536 = 241862843930939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4536 = (1567:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4537) ≤ val WuPaper.ClassicalFourthData.Bq 4537
    have hp : val WuPaper.ClassicalFourthData.Bq 4537 = (241880927465352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4537 = 241880927465352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4537 = (12537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4538) ≤ val WuPaper.ClassicalFourthData.Bq 4538
    have hp : val WuPaper.ClassicalFourthData.Bq 4538 = (241899003737719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4538 = 241899003737719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4538 = (6269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4539) ≤ val WuPaper.ClassicalFourthData.Bq 4539
    have hp : val WuPaper.ClassicalFourthData.Bq 4539 = (241917072750803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4539 = 241917072750803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4539 = (12539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4540) ≤ val WuPaper.ClassicalFourthData.Bq 4540
    have hp : val WuPaper.ClassicalFourthData.Bq 4540 = (241935134507365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4540 = 241935134507365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4540 = (627:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4541) ≤ val WuPaper.ClassicalFourthData.Bq 4541
    have hp : val WuPaper.ClassicalFourthData.Bq 4541 = (241953189010165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4541 = 241953189010165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4541 = (12541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4542) ≤ val WuPaper.ClassicalFourthData.Bq 4542
    have hp : val WuPaper.ClassicalFourthData.Bq 4542 = (241971236261963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4542 = 241971236261963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4542 = (6271:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4543) ≤ val WuPaper.ClassicalFourthData.Bq 4543
    have hp : val WuPaper.ClassicalFourthData.Bq 4543 = (241989276265516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4543 = 241989276265516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4543 = (12543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_283
