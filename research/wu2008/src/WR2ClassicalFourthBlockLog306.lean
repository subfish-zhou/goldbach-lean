import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints306
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_306 (j : Fin 16) (hj : 16*306+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*306+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*306+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4896) ≤ val WuPaper.ClassicalFourthData.Bq 4896
    have hp : val WuPaper.ClassicalFourthData.Bq 4896 = (247924124189931:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4896 = 247924124189931 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4896 = (403:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4897) ≤ val WuPaper.ClassicalFourthData.Bq 4897
    have hp : val WuPaper.ClassicalFourthData.Bq 4897 = (247939762779791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4897 = 247939762779791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4897 = (12897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4898) ≤ val WuPaper.ClassicalFourthData.Bq 4898
    have hp : val WuPaper.ClassicalFourthData.Bq 4898 = (247955395026814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4898 = 247955395026814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4898 = (6449:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4899) ≤ val WuPaper.ClassicalFourthData.Bq 4899
    have hp : val WuPaper.ClassicalFourthData.Bq 4899 = (247971020933355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4899 = 247971020933355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4899 = (12899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4900) ≤ val WuPaper.ClassicalFourthData.Bq 4900
    have hp : val WuPaper.ClassicalFourthData.Bq 4900 = (247986640501769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4900 = 247986640501769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4900 = (129:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4901) ≤ val WuPaper.ClassicalFourthData.Bq 4901
    have hp : val WuPaper.ClassicalFourthData.Bq 4901 = (248002253734410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4901 = 248002253734410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4901 = (12901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4902) ≤ val WuPaper.ClassicalFourthData.Bq 4902
    have hp : val WuPaper.ClassicalFourthData.Bq 4902 = (248017860633630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4902 = 248017860633630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4902 = (6451:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4903) ≤ val WuPaper.ClassicalFourthData.Bq 4903
    have hp : val WuPaper.ClassicalFourthData.Bq 4903 = (248033461201781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4903 = 248033461201781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4903 = (12903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4903
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4904) ≤ val WuPaper.ClassicalFourthData.Bq 4904
    have hp : val WuPaper.ClassicalFourthData.Bq 4904 = (248049055441214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4904 = 248049055441214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4904 = (1613:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4905) ≤ val WuPaper.ClassicalFourthData.Bq 4905
    have hp : val WuPaper.ClassicalFourthData.Bq 4905 = (248064643354277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4905 = 248064643354277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4905 = (2581:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4906) ≤ val WuPaper.ClassicalFourthData.Bq 4906
    have hp : val WuPaper.ClassicalFourthData.Bq 4906 = (248080224943320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4906 = 248080224943320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4906 = (6453:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4907) ≤ val WuPaper.ClassicalFourthData.Bq 4907
    have hp : val WuPaper.ClassicalFourthData.Bq 4907 = (248095800210690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4907 = 248095800210690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4907 = (12907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4908) ≤ val WuPaper.ClassicalFourthData.Bq 4908
    have hp : val WuPaper.ClassicalFourthData.Bq 4908 = (248111369158733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4908 = 248111369158733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4908 = (3227:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4909) ≤ val WuPaper.ClassicalFourthData.Bq 4909
    have hp : val WuPaper.ClassicalFourthData.Bq 4909 = (248126931789796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4909 = 248126931789796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4909 = (12909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4910) ≤ val WuPaper.ClassicalFourthData.Bq 4910
    have hp : val WuPaper.ClassicalFourthData.Bq 4910 = (248142488106221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4910 = 248142488106221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4910 = (1291:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4911) ≤ val WuPaper.ClassicalFourthData.Bq 4911
    have hp : val WuPaper.ClassicalFourthData.Bq 4911 = (248158038110354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4911 = 248158038110354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4911 = (12911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_306
