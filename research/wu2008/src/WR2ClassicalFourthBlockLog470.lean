import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints470
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_470 (j : Fin 16) (hj : 16*470+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*470+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*470+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7520) ≤ val WuPaper.ClassicalFourthData.Bq 7520
    have hp : val WuPaper.ClassicalFourthData.Bq 7520 = (272626364471327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7520 = 272626364471327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7520 = (97:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7520
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7521) ≤ val WuPaper.ClassicalFourthData.Bq 7521
    have hp : val WuPaper.ClassicalFourthData.Bq 7521 = (272631169624875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7521 = 272631169624875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7521 = (15521:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7521
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7522) ≤ val WuPaper.ClassicalFourthData.Bq 7522
    have hp : val WuPaper.ClassicalFourthData.Bq 7522 = (272635972217806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7522 = 272635972217806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7522 = (7761:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7522
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7523) ≤ val WuPaper.ClassicalFourthData.Bq 7523
    have hp : val WuPaper.ClassicalFourthData.Bq 7523 = (272640772250953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7523 = 272640772250953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7523 = (15523:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7523
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7524) ≤ val WuPaper.ClassicalFourthData.Bq 7524
    have hp : val WuPaper.ClassicalFourthData.Bq 7524 = (272645569725146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7524 = 272645569725146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7524 = (3881:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7524
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7525) ≤ val WuPaper.ClassicalFourthData.Bq 7525
    have hp : val WuPaper.ClassicalFourthData.Bq 7525 = (272650364641217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7525 = 272650364641217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7525 = (621:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7525
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7526) ≤ val WuPaper.ClassicalFourthData.Bq 7526
    have hp : val WuPaper.ClassicalFourthData.Bq 7526 = (272655156999997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7526 = 272655156999997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7526 = (7763:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7526
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7527) ≤ val WuPaper.ClassicalFourthData.Bq 7527
    have hp : val WuPaper.ClassicalFourthData.Bq 7527 = (272659946802316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7527 = 272659946802316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7527 = (15527:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7527
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7528) ≤ val WuPaper.ClassicalFourthData.Bq 7528
    have hp : val WuPaper.ClassicalFourthData.Bq 7528 = (272664734049006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7528 = 272664734049006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7528 = (1941:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7529) ≤ val WuPaper.ClassicalFourthData.Bq 7529
    have hp : val WuPaper.ClassicalFourthData.Bq 7529 = (272669518740894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7529 = 272669518740894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7529 = (15529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7530) ≤ val WuPaper.ClassicalFourthData.Bq 7530
    have hp : val WuPaper.ClassicalFourthData.Bq 7530 = (272674300878813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7530 = 272674300878813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7530 = (1553:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7531) ≤ val WuPaper.ClassicalFourthData.Bq 7531
    have hp : val WuPaper.ClassicalFourthData.Bq 7531 = (272679080463590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7531 = 272679080463590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7531 = (15531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7532) ≤ val WuPaper.ClassicalFourthData.Bq 7532
    have hp : val WuPaper.ClassicalFourthData.Bq 7532 = (272683857496055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7532 = 272683857496055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7532 = (3883:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7533) ≤ val WuPaper.ClassicalFourthData.Bq 7533
    have hp : val WuPaper.ClassicalFourthData.Bq 7533 = (272688631977037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7533 = 272688631977037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7533 = (15533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7534) ≤ val WuPaper.ClassicalFourthData.Bq 7534
    have hp : val WuPaper.ClassicalFourthData.Bq 7534 = (272693403907365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7534 = 272693403907365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7534 = (7767:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7535) ≤ val WuPaper.ClassicalFourthData.Bq 7535
    have hp : val WuPaper.ClassicalFourthData.Bq 7535 = (272698173287866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7535 = 272698173287866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7535 = (3107:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7535
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_470
