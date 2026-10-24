import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints046
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_046 (j : Fin 16) (hj : 16*46+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*46+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*46+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 736) ≤ val WuPaper.ClassicalFourthData.Bq 736
    have hp : val WuPaper.ClassicalFourthData.Bq 736 = (77334494716948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 736 = 77334494716948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 736 = (273:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 737) ≤ val WuPaper.ClassicalFourthData.Bq 737
    have hp : val WuPaper.ClassicalFourthData.Bq 737 = (77422301852684:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 737 = 77422301852684 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 737 = (8737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 738) ≤ val WuPaper.ClassicalFourthData.Bq 738
    have hp : val WuPaper.ClassicalFourthData.Bq 738 = (77510068490137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 738 = 77510068490137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 738 = (4369:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 739) ≤ val WuPaper.ClassicalFourthData.Bq 739
    have hp : val WuPaper.ClassicalFourthData.Bq 739 = (77597794651819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 739 = 77597794651819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 739 = (8739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 740) ≤ val WuPaper.ClassicalFourthData.Bq 740
    have hp : val WuPaper.ClassicalFourthData.Bq 740 = (77685480360227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 740 = 77685480360227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 740 = (437:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 741) ≤ val WuPaper.ClassicalFourthData.Bq 741
    have hp : val WuPaper.ClassicalFourthData.Bq 741 = (77773125637841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 741 = 77773125637841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 741 = (8741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 742) ≤ val WuPaper.ClassicalFourthData.Bq 742
    have hp : val WuPaper.ClassicalFourthData.Bq 742 = (77860730507126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 742 = 77860730507126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 742 = (4371:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 743) ≤ val WuPaper.ClassicalFourthData.Bq 743
    have hp : val WuPaper.ClassicalFourthData.Bq 743 = (77948294990532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 743 = 77948294990532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 743 = (8743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_743
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 744) ≤ val WuPaper.ClassicalFourthData.Bq 744
    have hp : val WuPaper.ClassicalFourthData.Bq 744 = (78035819110492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 744 = 78035819110492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 744 = (1093:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 745) ≤ val WuPaper.ClassicalFourthData.Bq 745
    have hp : val WuPaper.ClassicalFourthData.Bq 745 = (78123302889423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 745 = 78123302889423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 745 = (1749:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 746) ≤ val WuPaper.ClassicalFourthData.Bq 746
    have hp : val WuPaper.ClassicalFourthData.Bq 746 = (78210746349729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 746 = 78210746349729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 746 = (4373:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 747) ≤ val WuPaper.ClassicalFourthData.Bq 747
    have hp : val WuPaper.ClassicalFourthData.Bq 747 = (78298149513795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 747 = 78298149513795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 747 = (8747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 748) ≤ val WuPaper.ClassicalFourthData.Bq 748
    have hp : val WuPaper.ClassicalFourthData.Bq 748 = (78385512403993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 748 = 78385512403993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 748 = (2187:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 749) ≤ val WuPaper.ClassicalFourthData.Bq 749
    have hp : val WuPaper.ClassicalFourthData.Bq 749 = (78472835042677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 749 = 78472835042677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 749 = (8749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 750) ≤ val WuPaper.ClassicalFourthData.Bq 750
    have hp : val WuPaper.ClassicalFourthData.Bq 750 = (78560117452188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 750 = 78560117452188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 750 = (35:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 751) ≤ val WuPaper.ClassicalFourthData.Bq 751
    have hp : val WuPaper.ClassicalFourthData.Bq 751 = (78647359654848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 751 = 78647359654848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 751 = (8751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_046
