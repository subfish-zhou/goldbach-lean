import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints555
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_555 (j : Fin 16) (hj : 16*555+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*555+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*555+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8880) ≤ val WuPaper.ClassicalFourthData.Bq 8880
    have hp : val WuPaper.ClassicalFourthData.Bq 8880 = (277104587575987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8880 = 277104587575987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8880 = (211:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8881) ≤ val WuPaper.ClassicalFourthData.Bq 8881
    have hp : val WuPaper.ClassicalFourthData.Bq 8881 = (277106568641297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8881 = 277106568641297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8881 = (16881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8882) ≤ val WuPaper.ClassicalFourthData.Bq 8882
    have hp : val WuPaper.ClassicalFourthData.Bq 8882 = (277108548043883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8882 = 277108548043883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8882 = (8441:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8883) ≤ val WuPaper.ClassicalFourthData.Bq 8883
    have hp : val WuPaper.ClassicalFourthData.Bq 8883 = (277110525784262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8883 = 277110525784262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8883 = (16883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8884) ≤ val WuPaper.ClassicalFourthData.Bq 8884
    have hp : val WuPaper.ClassicalFourthData.Bq 8884 = (277112501862951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8884 = 277112501862951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8884 = (4221:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8885) ≤ val WuPaper.ClassicalFourthData.Bq 8885
    have hp : val WuPaper.ClassicalFourthData.Bq 8885 = (277114476280466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8885 = 277114476280466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8885 = (3377:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8886) ≤ val WuPaper.ClassicalFourthData.Bq 8886
    have hp : val WuPaper.ClassicalFourthData.Bq 8886 = (277116449037325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8886 = 277116449037325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8886 = (8443:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8887) ≤ val WuPaper.ClassicalFourthData.Bq 8887
    have hp : val WuPaper.ClassicalFourthData.Bq 8887 = (277118420134043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8887 = 277118420134043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8887 = (16887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8887
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8888) ≤ val WuPaper.ClassicalFourthData.Bq 8888
    have hp : val WuPaper.ClassicalFourthData.Bq 8888 = (277120389571138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8888 = 277120389571138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8888 = (2111:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8889) ≤ val WuPaper.ClassicalFourthData.Bq 8889
    have hp : val WuPaper.ClassicalFourthData.Bq 8889 = (277122357349124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8889 = 277122357349124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8889 = (16889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8890) ≤ val WuPaper.ClassicalFourthData.Bq 8890
    have hp : val WuPaper.ClassicalFourthData.Bq 8890 = (277124323468518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8890 = 277124323468518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8890 = (1689:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8891) ≤ val WuPaper.ClassicalFourthData.Bq 8891
    have hp : val WuPaper.ClassicalFourthData.Bq 8891 = (277126287929837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8891 = 277126287929837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8891 = (16891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8892) ≤ val WuPaper.ClassicalFourthData.Bq 8892
    have hp : val WuPaper.ClassicalFourthData.Bq 8892 = (277128250733594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8892 = 277128250733594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8892 = (4223:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8893) ≤ val WuPaper.ClassicalFourthData.Bq 8893
    have hp : val WuPaper.ClassicalFourthData.Bq 8893 = (277130211880306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8893 = 277130211880306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8893 = (16893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8894) ≤ val WuPaper.ClassicalFourthData.Bq 8894
    have hp : val WuPaper.ClassicalFourthData.Bq 8894 = (277132171370489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8894 = 277132171370489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8894 = (8447:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8895) ≤ val WuPaper.ClassicalFourthData.Bq 8895
    have hp : val WuPaper.ClassicalFourthData.Bq 8895 = (277134129204656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8895 = 277134129204656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8895 = (3379:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_555
