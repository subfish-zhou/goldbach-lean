import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints040
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_040 (j : Fin 16) (hj : 16*40+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*40+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*40+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 640) ≤ val WuPaper.ClassicalFourthData.Bq 640
    have hp : val WuPaper.ClassicalFourthData.Bq 640 = (68712965332534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 640 = 68712965332534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 640 = (54:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 641) ≤ val WuPaper.ClassicalFourthData.Bq 641
    have hp : val WuPaper.ClassicalFourthData.Bq 641 = (68804767568175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 641 = 68804767568175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 641 = (8641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 642) ≤ val WuPaper.ClassicalFourthData.Bq 642
    have hp : val WuPaper.ClassicalFourthData.Bq 642 = (68896527068899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 642 = 68896527068899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 642 = (4321:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 643) ≤ val WuPaper.ClassicalFourthData.Bq 643
    have hp : val WuPaper.ClassicalFourthData.Bq 643 = (68988243858797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 643 = 68988243858797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 643 = (8643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 644) ≤ val WuPaper.ClassicalFourthData.Bq 644
    have hp : val WuPaper.ClassicalFourthData.Bq 644 = (69079917961941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 644 = 69079917961941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 644 = (2161:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 645) ≤ val WuPaper.ClassicalFourthData.Bq 645
    have hp : val WuPaper.ClassicalFourthData.Bq 645 = (69171549402389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 645 = 69171549402389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 645 = (1729:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 646) ≤ val WuPaper.ClassicalFourthData.Bq 646
    have hp : val WuPaper.ClassicalFourthData.Bq 646 = (69263138204177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 646 = 69263138204177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 646 = (4323:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 647) ≤ val WuPaper.ClassicalFourthData.Bq 647
    have hp : val WuPaper.ClassicalFourthData.Bq 647 = (69354684391327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 647 = 69354684391327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 647 = (8647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_647
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 648) ≤ val WuPaper.ClassicalFourthData.Bq 648
    have hp : val WuPaper.ClassicalFourthData.Bq 648 = (69446187987845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 648 = 69446187987845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 648 = (1081:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 649) ≤ val WuPaper.ClassicalFourthData.Bq 649
    have hp : val WuPaper.ClassicalFourthData.Bq 649 = (69537649017717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 649 = 69537649017717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 649 = (8649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 650) ≤ val WuPaper.ClassicalFourthData.Bq 650
    have hp : val WuPaper.ClassicalFourthData.Bq 650 = (69629067504913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 650 = 69629067504913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 650 = (173:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 651) ≤ val WuPaper.ClassicalFourthData.Bq 651
    have hp : val WuPaper.ClassicalFourthData.Bq 651 = (69720443473388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 651 = 69720443473388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 651 = (8651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 652) ≤ val WuPaper.ClassicalFourthData.Bq 652
    have hp : val WuPaper.ClassicalFourthData.Bq 652 = (69811776947077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 652 = 69811776947077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 652 = (2163:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 653) ≤ val WuPaper.ClassicalFourthData.Bq 653
    have hp : val WuPaper.ClassicalFourthData.Bq 653 = (69903067949900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 653 = 69903067949900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 653 = (8653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 654) ≤ val WuPaper.ClassicalFourthData.Bq 654
    have hp : val WuPaper.ClassicalFourthData.Bq 654 = (69994316505759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 654 = 69994316505759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 654 = (4327:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 655) ≤ val WuPaper.ClassicalFourthData.Bq 655
    have hp : val WuPaper.ClassicalFourthData.Bq 655 = (70085522638540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 655 = 70085522638540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 655 = (1731:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_040
