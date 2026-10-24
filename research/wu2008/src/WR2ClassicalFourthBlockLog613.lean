import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints613
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_613 (j : Fin 16) (hj : 16*613+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*613+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*613+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9808) ≤ val WuPaper.ClassicalFourthData.Bq 9808
    have hp : val WuPaper.ClassicalFourthData.Bq 9808 = (278291503434743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9808 = 278291503434743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9808 = (1113:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9809) ≤ val WuPaper.ClassicalFourthData.Bq 9809
    have hp : val WuPaper.ClassicalFourthData.Bq 9809 = (278292142726427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9809 = 278292142726427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9809 = (17809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9810) ≤ val WuPaper.ClassicalFourthData.Bq 9810
    have hp : val WuPaper.ClassicalFourthData.Bq 9810 = (278292780768519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9810 = 278292780768519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9810 = (1781:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9811) ≤ val WuPaper.ClassicalFourthData.Bq 9811
    have hp : val WuPaper.ClassicalFourthData.Bq 9811 = (278293417561403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9811 = 278293417561403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9811 = (17811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9812) ≤ val WuPaper.ClassicalFourthData.Bq 9812
    have hp : val WuPaper.ClassicalFourthData.Bq 9812 = (278294053105458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9812 = 278294053105458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9812 = (4453:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9813) ≤ val WuPaper.ClassicalFourthData.Bq 9813
    have hp : val WuPaper.ClassicalFourthData.Bq 9813 = (278294687401065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9813 = 278294687401065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9813 = (17813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9814) ≤ val WuPaper.ClassicalFourthData.Bq 9814
    have hp : val WuPaper.ClassicalFourthData.Bq 9814 = (278295320448606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9814 = 278295320448606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9814 = (8907:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9815) ≤ val WuPaper.ClassicalFourthData.Bq 9815
    have hp : val WuPaper.ClassicalFourthData.Bq 9815 = (278295952248460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9815 = 278295952248460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9815 = (3563:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9815
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9816) ≤ val WuPaper.ClassicalFourthData.Bq 9816
    have hp : val WuPaper.ClassicalFourthData.Bq 9816 = (278296582801008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9816 = 278296582801008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9816 = (2227:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9817) ≤ val WuPaper.ClassicalFourthData.Bq 9817
    have hp : val WuPaper.ClassicalFourthData.Bq 9817 = (278297212106630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9817 = 278297212106630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9817 = (17817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9818) ≤ val WuPaper.ClassicalFourthData.Bq 9818
    have hp : val WuPaper.ClassicalFourthData.Bq 9818 = (278297840165707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9818 = 278297840165707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9818 = (8909:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9819) ≤ val WuPaper.ClassicalFourthData.Bq 9819
    have hp : val WuPaper.ClassicalFourthData.Bq 9819 = (278298466978619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9819 = 278298466978619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9819 = (17819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9820) ≤ val WuPaper.ClassicalFourthData.Bq 9820
    have hp : val WuPaper.ClassicalFourthData.Bq 9820 = (278299092545745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9820 = 278299092545745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9820 = (891:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9821) ≤ val WuPaper.ClassicalFourthData.Bq 9821
    have hp : val WuPaper.ClassicalFourthData.Bq 9821 = (278299716867465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9821 = 278299716867465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9821 = (17821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9822) ≤ val WuPaper.ClassicalFourthData.Bq 9822
    have hp : val WuPaper.ClassicalFourthData.Bq 9822 = (278300339944159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9822 = 278300339944159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9822 = (8911:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9823) ≤ val WuPaper.ClassicalFourthData.Bq 9823
    have hp : val WuPaper.ClassicalFourthData.Bq 9823 = (278300961776207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9823 = 278300961776207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9823 = (17823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9823
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_613
