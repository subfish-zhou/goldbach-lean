import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints538
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_538 (j : Fin 16) (hj : 16*538+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*538+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*538+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8608) ≤ val WuPaper.ClassicalFourthData.Bq 8608
    have hp : val WuPaper.ClassicalFourthData.Bq 8608 = (276502209056903:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8608 = 276502209056903 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8608 = (519:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8609) ≤ val WuPaper.ClassicalFourthData.Bq 8609
    have hp : val WuPaper.ClassicalFourthData.Bq 8609 = (276504662190341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8609 = 276504662190341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8609 = (16609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8610) ≤ val WuPaper.ClassicalFourthData.Bq 8610
    have hp : val WuPaper.ClassicalFourthData.Bq 8610 = (276507113513690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8610 = 276507113513690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8610 = (1661:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8611) ≤ val WuPaper.ClassicalFourthData.Bq 8611
    have hp : val WuPaper.ClassicalFourthData.Bq 8611 = (276509563027518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8611 = 276509563027518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8611 = (16611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8612) ≤ val WuPaper.ClassicalFourthData.Bq 8612
    have hp : val WuPaper.ClassicalFourthData.Bq 8612 = (276512010732391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8612 = 276512010732391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8612 = (4153:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8613) ≤ val WuPaper.ClassicalFourthData.Bq 8613
    have hp : val WuPaper.ClassicalFourthData.Bq 8613 = (276514456628875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8613 = 276514456628875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8613 = (16613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8614) ≤ val WuPaper.ClassicalFourthData.Bq 8614
    have hp : val WuPaper.ClassicalFourthData.Bq 8614 = (276516900717539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8614 = 276516900717539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8614 = (8307:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8615) ≤ val WuPaper.ClassicalFourthData.Bq 8615
    have hp : val WuPaper.ClassicalFourthData.Bq 8615 = (276519342998947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8615 = 276519342998947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8615 = (3323:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8615
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8616) ≤ val WuPaper.ClassicalFourthData.Bq 8616
    have hp : val WuPaper.ClassicalFourthData.Bq 8616 = (276521783473666:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8616 = 276521783473666 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8616 = (2077:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8617) ≤ val WuPaper.ClassicalFourthData.Bq 8617
    have hp : val WuPaper.ClassicalFourthData.Bq 8617 = (276524222142262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8617 = 276524222142262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8617 = (16617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8618) ≤ val WuPaper.ClassicalFourthData.Bq 8618
    have hp : val WuPaper.ClassicalFourthData.Bq 8618 = (276526659005301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8618 = 276526659005301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8618 = (8309:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8619) ≤ val WuPaper.ClassicalFourthData.Bq 8619
    have hp : val WuPaper.ClassicalFourthData.Bq 8619 = (276529094063348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8619 = 276529094063348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8619 = (16619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8620) ≤ val WuPaper.ClassicalFourthData.Bq 8620
    have hp : val WuPaper.ClassicalFourthData.Bq 8620 = (276531527316969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8620 = 276531527316969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8620 = (831:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8621) ≤ val WuPaper.ClassicalFourthData.Bq 8621
    have hp : val WuPaper.ClassicalFourthData.Bq 8621 = (276533958766728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8621 = 276533958766728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8621 = (16621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8622) ≤ val WuPaper.ClassicalFourthData.Bq 8622
    have hp : val WuPaper.ClassicalFourthData.Bq 8622 = (276536388413192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8622 = 276536388413192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8622 = (8311:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8623) ≤ val WuPaper.ClassicalFourthData.Bq 8623
    have hp : val WuPaper.ClassicalFourthData.Bq 8623 = (276538816256924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8623 = 276538816256924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8623 = (16623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_538
