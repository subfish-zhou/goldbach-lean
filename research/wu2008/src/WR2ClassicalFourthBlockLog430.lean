import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints430
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_430 (j : Fin 16) (hj : 16*430+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*430+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*430+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6880) ≤ val WuPaper.ClassicalFourthData.Bq 6880
    have hp : val WuPaper.ClassicalFourthData.Bq 6880 = (268987064598951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6880 = 268987064598951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6880 = (93:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6881) ≤ val WuPaper.ClassicalFourthData.Bq 6881
    have hp : val WuPaper.ClassicalFourthData.Bq 6881 = (268993693394040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6881 = 268993693394040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6881 = (14881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6882) ≤ val WuPaper.ClassicalFourthData.Bq 6882
    have hp : val WuPaper.ClassicalFourthData.Bq 6882 = (269000319028097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6882 = 269000319028097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6882 = (7441:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6883) ≤ val WuPaper.ClassicalFourthData.Bq 6883
    have hp : val WuPaper.ClassicalFourthData.Bq 6883 = (269006941502178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6883 = 269006941502178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6883 = (14883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6884) ≤ val WuPaper.ClassicalFourthData.Bq 6884
    have hp : val WuPaper.ClassicalFourthData.Bq 6884 = (269013560817335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6884 = 269013560817335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6884 = (3721:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6885) ≤ val WuPaper.ClassicalFourthData.Bq 6885
    have hp : val WuPaper.ClassicalFourthData.Bq 6885 = (269020176974623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6885 = 269020176974623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6885 = (2977:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6886) ≤ val WuPaper.ClassicalFourthData.Bq 6886
    have hp : val WuPaper.ClassicalFourthData.Bq 6886 = (269026789975094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6886 = 269026789975094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6886 = (7443:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6887) ≤ val WuPaper.ClassicalFourthData.Bq 6887
    have hp : val WuPaper.ClassicalFourthData.Bq 6887 = (269033399819802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6887 = 269033399819802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6887 = (14887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6887
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6888) ≤ val WuPaper.ClassicalFourthData.Bq 6888
    have hp : val WuPaper.ClassicalFourthData.Bq 6888 = (269040006509798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6888 = 269040006509798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6888 = (1861:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6889) ≤ val WuPaper.ClassicalFourthData.Bq 6889
    have hp : val WuPaper.ClassicalFourthData.Bq 6889 = (269046610046136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6889 = 269046610046136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6889 = (14889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6890) ≤ val WuPaper.ClassicalFourthData.Bq 6890
    have hp : val WuPaper.ClassicalFourthData.Bq 6890 = (269053210429866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6890 = 269053210429866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6890 = (1489:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6891) ≤ val WuPaper.ClassicalFourthData.Bq 6891
    have hp : val WuPaper.ClassicalFourthData.Bq 6891 = (269059807662039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6891 = 269059807662039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6891 = (14891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6892) ≤ val WuPaper.ClassicalFourthData.Bq 6892
    have hp : val WuPaper.ClassicalFourthData.Bq 6892 = (269066401743707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6892 = 269066401743707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6892 = (3723:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6893) ≤ val WuPaper.ClassicalFourthData.Bq 6893
    have hp : val WuPaper.ClassicalFourthData.Bq 6893 = (269072992675919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6893 = 269072992675919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6893 = (14893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6894) ≤ val WuPaper.ClassicalFourthData.Bq 6894
    have hp : val WuPaper.ClassicalFourthData.Bq 6894 = (269079580459726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6894 = 269079580459726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6894 = (7447:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6895) ≤ val WuPaper.ClassicalFourthData.Bq 6895
    have hp : val WuPaper.ClassicalFourthData.Bq 6895 = (269086165096178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6895 = 269086165096178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6895 = (2979:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_430
