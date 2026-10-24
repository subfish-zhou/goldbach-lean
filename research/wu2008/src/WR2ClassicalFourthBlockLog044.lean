import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints044
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_044 (j : Fin 16) (hj : 16*44+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*44+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*44+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 704) ≤ val WuPaper.ClassicalFourthData.Bq 704
    have hp : val WuPaper.ClassicalFourthData.Bq 704 = (74503147737333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 704 = 74503147737333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 704 = (272:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 705) ≤ val WuPaper.ClassicalFourthData.Bq 705
    have hp : val WuPaper.ClassicalFourthData.Bq 705 = (74592262799519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 705 = 74592262799519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 705 = (1741:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 706) ≤ val WuPaper.ClassicalFourthData.Bq 706
    have hp : val WuPaper.ClassicalFourthData.Bq 706 = (74681336634634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 706 = 74681336634634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 706 = (4353:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 707) ≤ val WuPaper.ClassicalFourthData.Bq 707
    have hp : val WuPaper.ClassicalFourthData.Bq 707 = (74770369265701:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 707 = 74770369265701 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 707 = (8707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 708) ≤ val WuPaper.ClassicalFourthData.Bq 708
    have hp : val WuPaper.ClassicalFourthData.Bq 708 = (74859360715728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 708 = 74859360715728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 708 = (2177:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 709) ≤ val WuPaper.ClassicalFourthData.Bq 709
    have hp : val WuPaper.ClassicalFourthData.Bq 709 = (74948311007706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 709 = 74948311007706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 709 = (8709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 710) ≤ val WuPaper.ClassicalFourthData.Bq 710
    have hp : val WuPaper.ClassicalFourthData.Bq 710 = (75037220164609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 710 = 75037220164609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 710 = (871:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 711) ≤ val WuPaper.ClassicalFourthData.Bq 711
    have hp : val WuPaper.ClassicalFourthData.Bq 711 = (75126088209397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 711 = 75126088209397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 711 = (8711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_711
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 712) ≤ val WuPaper.ClassicalFourthData.Bq 712
    have hp : val WuPaper.ClassicalFourthData.Bq 712 = (75214915165012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 712 = 75214915165012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 712 = (1089:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 713) ≤ val WuPaper.ClassicalFourthData.Bq 713
    have hp : val WuPaper.ClassicalFourthData.Bq 713 = (75303701054380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 713 = 75303701054380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 713 = (8713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 714) ≤ val WuPaper.ClassicalFourthData.Bq 714
    have hp : val WuPaper.ClassicalFourthData.Bq 714 = (75392445900413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 714 = 75392445900413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 714 = (4357:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 715) ≤ val WuPaper.ClassicalFourthData.Bq 715
    have hp : val WuPaper.ClassicalFourthData.Bq 715 = (75481149726004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 715 = 75481149726004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 715 = (1743:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 716) ≤ val WuPaper.ClassicalFourthData.Bq 716
    have hp : val WuPaper.ClassicalFourthData.Bq 716 = (75569812554032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 716 = 75569812554032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 716 = (2179:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 717) ≤ val WuPaper.ClassicalFourthData.Bq 717
    have hp : val WuPaper.ClassicalFourthData.Bq 717 = (75658434407358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 717 = 75658434407358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 717 = (8717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 718) ≤ val WuPaper.ClassicalFourthData.Bq 718
    have hp : val WuPaper.ClassicalFourthData.Bq 718 = (75747015308829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 718 = 75747015308829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 718 = (4359:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 719) ≤ val WuPaper.ClassicalFourthData.Bq 719
    have hp : val WuPaper.ClassicalFourthData.Bq 719 = (75835555281276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 719 = 75835555281276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 719 = (8719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_044
