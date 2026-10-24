import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints425
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_425 (j : Fin 16) (hj : 16*425+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*425+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*425+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6800) ≤ val WuPaper.ClassicalFourthData.Bq 6800
    have hp : val WuPaper.ClassicalFourthData.Bq 6800 = (268446425137957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6800 = 268446425137957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6800 = (37:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6801) ≤ val WuPaper.ClassicalFourthData.Bq 6801
    have hp : val WuPaper.ClassicalFourthData.Bq 6801 = (268453310267307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6801 = 268453310267307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6801 = (14801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6802) ≤ val WuPaper.ClassicalFourthData.Bq 6802
    have hp : val WuPaper.ClassicalFourthData.Bq 6802 = (268460192149970:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6802 = 268460192149970 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6802 = (7401:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6803) ≤ val WuPaper.ClassicalFourthData.Bq 6803
    have hp : val WuPaper.ClassicalFourthData.Bq 6803 = (268467070787034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6803 = 268467070787034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6803 = (14803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6804) ≤ val WuPaper.ClassicalFourthData.Bq 6804
    have hp : val WuPaper.ClassicalFourthData.Bq 6804 = (268473946179583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6804 = 268473946179583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6804 = (3701:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6805) ≤ val WuPaper.ClassicalFourthData.Bq 6805
    have hp : val WuPaper.ClassicalFourthData.Bq 6805 = (268480818328704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6805 = 268480818328704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6805 = (2961:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6806) ≤ val WuPaper.ClassicalFourthData.Bq 6806
    have hp : val WuPaper.ClassicalFourthData.Bq 6806 = (268487687235483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6806 = 268487687235483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6806 = (7403:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6807) ≤ val WuPaper.ClassicalFourthData.Bq 6807
    have hp : val WuPaper.ClassicalFourthData.Bq 6807 = (268494552901005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6807 = 268494552901005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6807 = (14807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6807
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6808) ≤ val WuPaper.ClassicalFourthData.Bq 6808
    have hp : val WuPaper.ClassicalFourthData.Bq 6808 = (268501415326355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6808 = 268501415326355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6808 = (1851:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6809) ≤ val WuPaper.ClassicalFourthData.Bq 6809
    have hp : val WuPaper.ClassicalFourthData.Bq 6809 = (268508274512617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6809 = 268508274512617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6809 = (14809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6810) ≤ val WuPaper.ClassicalFourthData.Bq 6810
    have hp : val WuPaper.ClassicalFourthData.Bq 6810 = (268515130460874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6810 = 268515130460874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6810 = (1481:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6811) ≤ val WuPaper.ClassicalFourthData.Bq 6811
    have hp : val WuPaper.ClassicalFourthData.Bq 6811 = (268521983172211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6811 = 268521983172211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6811 = (14811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6812) ≤ val WuPaper.ClassicalFourthData.Bq 6812
    have hp : val WuPaper.ClassicalFourthData.Bq 6812 = (268528832647710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6812 = 268528832647710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6812 = (3703:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6813) ≤ val WuPaper.ClassicalFourthData.Bq 6813
    have hp : val WuPaper.ClassicalFourthData.Bq 6813 = (268535678888455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6813 = 268535678888455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6813 = (14813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6814) ≤ val WuPaper.ClassicalFourthData.Bq 6814
    have hp : val WuPaper.ClassicalFourthData.Bq 6814 = (268542521895527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6814 = 268542521895527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6814 = (7407:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6815) ≤ val WuPaper.ClassicalFourthData.Bq 6815
    have hp : val WuPaper.ClassicalFourthData.Bq 6815 = (268549361670008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6815 = 268549361670008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6815 = (2963:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_425
