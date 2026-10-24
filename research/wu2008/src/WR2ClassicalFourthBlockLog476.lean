import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints476
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_476 (j : Fin 16) (hj : 16*476+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*476+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*476+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7616) ≤ val WuPaper.ClassicalFourthData.Bq 7616
    have hp : val WuPaper.ClassicalFourthData.Bq 7616 = (273076100656675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7616 = 273076100656675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7616 = (488:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7617) ≤ val WuPaper.ClassicalFourthData.Bq 7617
    have hp : val WuPaper.ClassicalFourthData.Bq 7617 = (273080663741451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7617 = 273080663741451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7617 = (15617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7618) ≤ val WuPaper.ClassicalFourthData.Bq 7618
    have hp : val WuPaper.ClassicalFourthData.Bq 7618 = (273085224344107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7618 = 273085224344107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7618 = (7809:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7619) ≤ val WuPaper.ClassicalFourthData.Bq 7619
    have hp : val WuPaper.ClassicalFourthData.Bq 7619 = (273089782465446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7619 = 273089782465446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7619 = (15619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7620) ≤ val WuPaper.ClassicalFourthData.Bq 7620
    have hp : val WuPaper.ClassicalFourthData.Bq 7620 = (273094338106272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7620 = 273094338106272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7620 = (781:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7621) ≤ val WuPaper.ClassicalFourthData.Bq 7621
    have hp : val WuPaper.ClassicalFourthData.Bq 7621 = (273098891267388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7621 = 273098891267388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7621 = (15621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7622) ≤ val WuPaper.ClassicalFourthData.Bq 7622
    have hp : val WuPaper.ClassicalFourthData.Bq 7622 = (273103441949596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7622 = 273103441949596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7622 = (7811:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7623) ≤ val WuPaper.ClassicalFourthData.Bq 7623
    have hp : val WuPaper.ClassicalFourthData.Bq 7623 = (273107990153698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7623 = 273107990153698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7623 = (15623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7623
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7624) ≤ val WuPaper.ClassicalFourthData.Bq 7624
    have hp : val WuPaper.ClassicalFourthData.Bq 7624 = (273112535880497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7624 = 273112535880497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7624 = (1953:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7625) ≤ val WuPaper.ClassicalFourthData.Bq 7625
    have hp : val WuPaper.ClassicalFourthData.Bq 7625 = (273117079130793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7625 = 273117079130793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7625 = (125:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7626) ≤ val WuPaper.ClassicalFourthData.Bq 7626
    have hp : val WuPaper.ClassicalFourthData.Bq 7626 = (273121619905389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7626 = 273121619905389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7626 = (7813:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7627) ≤ val WuPaper.ClassicalFourthData.Bq 7627
    have hp : val WuPaper.ClassicalFourthData.Bq 7627 = (273126158205085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7627 = 273126158205085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7627 = (15627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7628) ≤ val WuPaper.ClassicalFourthData.Bq 7628
    have hp : val WuPaper.ClassicalFourthData.Bq 7628 = (273130694030683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7628 = 273130694030683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7628 = (3907:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7629) ≤ val WuPaper.ClassicalFourthData.Bq 7629
    have hp : val WuPaper.ClassicalFourthData.Bq 7629 = (273135227382982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7629 = 273135227382982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7629 = (15629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7630) ≤ val WuPaper.ClassicalFourthData.Bq 7630
    have hp : val WuPaper.ClassicalFourthData.Bq 7630 = (273139758262784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7630 = 273139758262784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7630 = (1563:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7631) ≤ val WuPaper.ClassicalFourthData.Bq 7631
    have hp : val WuPaper.ClassicalFourthData.Bq 7631 = (273144286670887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7631 = 273144286670887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7631 = (15631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7631
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_476
