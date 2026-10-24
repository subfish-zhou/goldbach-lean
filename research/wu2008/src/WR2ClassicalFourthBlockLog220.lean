import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints220
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_220 (j : Fin 16) (hj : 16*220+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*220+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*220+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3520) ≤ val WuPaper.ClassicalFourthData.Bq 3520
    have hp : val WuPaper.ClassicalFourthData.Bq 3520 = (219191589181201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3520 = 219191589181201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3520 = (72:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3521) ≤ val WuPaper.ClassicalFourthData.Bq 3521
    have hp : val WuPaper.ClassicalFourthData.Bq 3521 = (219218729875662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3521 = 219218729875662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3521 = (11521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3522) ≤ val WuPaper.ClassicalFourthData.Bq 3522
    have hp : val WuPaper.ClassicalFourthData.Bq 3522 = (219245859721665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3522 = 219245859721665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3522 = (5761:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3523) ≤ val WuPaper.ClassicalFourthData.Bq 3523
    have hp : val WuPaper.ClassicalFourthData.Bq 3523 = (219272978723664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3523 = 219272978723664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3523 = (11523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3524) ≤ val WuPaper.ClassicalFourthData.Bq 3524
    have hp : val WuPaper.ClassicalFourthData.Bq 3524 = (219300086886114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3524 = 219300086886114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3524 = (2881:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3525) ≤ val WuPaper.ClassicalFourthData.Bq 3525
    have hp : val WuPaper.ClassicalFourthData.Bq 3525 = (219327184213466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3525 = 219327184213466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3525 = (461:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3526) ≤ val WuPaper.ClassicalFourthData.Bq 3526
    have hp : val WuPaper.ClassicalFourthData.Bq 3526 = (219354270710171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3526 = 219354270710171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3526 = (5763:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3527) ≤ val WuPaper.ClassicalFourthData.Bq 3527
    have hp : val WuPaper.ClassicalFourthData.Bq 3527 = (219381346380673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3527 = 219381346380673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3527 = (11527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3527
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3528) ≤ val WuPaper.ClassicalFourthData.Bq 3528
    have hp : val WuPaper.ClassicalFourthData.Bq 3528 = (219408411229420:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3528 = 219408411229420 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3528 = (1441:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3529) ≤ val WuPaper.ClassicalFourthData.Bq 3529
    have hp : val WuPaper.ClassicalFourthData.Bq 3529 = (219435465260854:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3529 = 219435465260854 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3529 = (11529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3530) ≤ val WuPaper.ClassicalFourthData.Bq 3530
    have hp : val WuPaper.ClassicalFourthData.Bq 3530 = (219462508479415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3530 = 219462508479415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3530 = (1153:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3531) ≤ val WuPaper.ClassicalFourthData.Bq 3531
    have hp : val WuPaper.ClassicalFourthData.Bq 3531 = (219489540889541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3531 = 219489540889541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3531 = (11531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3532) ≤ val WuPaper.ClassicalFourthData.Bq 3532
    have hp : val WuPaper.ClassicalFourthData.Bq 3532 = (219516562495670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3532 = 219516562495670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3532 = (2883:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3533) ≤ val WuPaper.ClassicalFourthData.Bq 3533
    have hp : val WuPaper.ClassicalFourthData.Bq 3533 = (219543573302235:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3533 = 219543573302235 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3533 = (11533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3534) ≤ val WuPaper.ClassicalFourthData.Bq 3534
    have hp : val WuPaper.ClassicalFourthData.Bq 3534 = (219570573313667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3534 = 219570573313667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3534 = (5767:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3535) ≤ val WuPaper.ClassicalFourthData.Bq 3535
    have hp : val WuPaper.ClassicalFourthData.Bq 3535 = (219597562534398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3535 = 219597562534398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3535 = (2307:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_220
