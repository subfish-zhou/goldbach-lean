import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints594
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_594 (j : Fin 16) (hj : 16*594+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*594+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*594+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9504) ≤ val WuPaper.ClassicalFourthData.Bq 9504
    have hp : val WuPaper.ClassicalFourthData.Bq 9504 = (278037380433377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9504 = 278037380433377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9504 = (547:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9505) ≤ val WuPaper.ClassicalFourthData.Bq 9505
    have hp : val WuPaper.ClassicalFourthData.Bq 9505 = (278038417861756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9505 = 278038417861756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9505 = (3501:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9506) ≤ val WuPaper.ClassicalFourthData.Bq 9506
    have hp : val WuPaper.ClassicalFourthData.Bq 9506 = (278039453918805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9506 = 278039453918805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9506 = (8753:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9507) ≤ val WuPaper.ClassicalFourthData.Bq 9507
    have hp : val WuPaper.ClassicalFourthData.Bq 9507 = (278040488604946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9507 = 278040488604946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9507 = (17507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9508) ≤ val WuPaper.ClassicalFourthData.Bq 9508
    have hp : val WuPaper.ClassicalFourthData.Bq 9508 = (278041521920600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9508 = 278041521920600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9508 = (4377:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9509) ≤ val WuPaper.ClassicalFourthData.Bq 9509
    have hp : val WuPaper.ClassicalFourthData.Bq 9509 = (278042553866186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9509 = 278042553866186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9509 = (17509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9510) ≤ val WuPaper.ClassicalFourthData.Bq 9510
    have hp : val WuPaper.ClassicalFourthData.Bq 9510 = (278043584442124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9510 = 278043584442124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9510 = (1751:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9511) ≤ val WuPaper.ClassicalFourthData.Bq 9511
    have hp : val WuPaper.ClassicalFourthData.Bq 9511 = (278044613648834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9511 = 278044613648834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9511 = (17511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9511
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9512) ≤ val WuPaper.ClassicalFourthData.Bq 9512
    have hp : val WuPaper.ClassicalFourthData.Bq 9512 = (278045641486736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9512 = 278045641486736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9512 = (2189:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9513) ≤ val WuPaper.ClassicalFourthData.Bq 9513
    have hp : val WuPaper.ClassicalFourthData.Bq 9513 = (278046667956251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9513 = 278046667956251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9513 = (17513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9514) ≤ val WuPaper.ClassicalFourthData.Bq 9514
    have hp : val WuPaper.ClassicalFourthData.Bq 9514 = (278047693057796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9514 = 278047693057796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9514 = (8757:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9515) ≤ val WuPaper.ClassicalFourthData.Bq 9515
    have hp : val WuPaper.ClassicalFourthData.Bq 9515 = (278048716791792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9515 = 278048716791792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9515 = (3503:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9516) ≤ val WuPaper.ClassicalFourthData.Bq 9516
    have hp : val WuPaper.ClassicalFourthData.Bq 9516 = (278049739158659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9516 = 278049739158659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9516 = (4379:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9517) ≤ val WuPaper.ClassicalFourthData.Bq 9517
    have hp : val WuPaper.ClassicalFourthData.Bq 9517 = (278050760158814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9517 = 278050760158814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9517 = (17517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9518) ≤ val WuPaper.ClassicalFourthData.Bq 9518
    have hp : val WuPaper.ClassicalFourthData.Bq 9518 = (278051779792677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9518 = 278051779792677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9518 = (8759:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9519) ≤ val WuPaper.ClassicalFourthData.Bq 9519
    have hp : val WuPaper.ClassicalFourthData.Bq 9519 = (278052798060668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9519 = 278052798060668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9519 = (17519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_594
