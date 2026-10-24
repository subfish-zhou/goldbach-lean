import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints055
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_055 (j : Fin 16) (hj : 16*55+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*55+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*55+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 880) ≤ val WuPaper.ClassicalFourthData.Bq 880
    have hp : val WuPaper.ClassicalFourthData.Bq 880 = (89572458894219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 880 = 89572458894219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 880 = (111:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 881) ≤ val WuPaper.ClassicalFourthData.Bq 881
    have hp : val WuPaper.ClassicalFourthData.Bq 881 = (89654658612823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 881 = 89654658612823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 881 = (8881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 882) ≤ val WuPaper.ClassicalFourthData.Bq 882
    have hp : val WuPaper.ClassicalFourthData.Bq 882 = (89736820919108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 882 = 89736820919108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 882 = (4441:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 883) ≤ val WuPaper.ClassicalFourthData.Bq 883
    have hp : val WuPaper.ClassicalFourthData.Bq 883 = (89818945833450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 883 = 89818945833450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 883 = (8883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 884) ≤ val WuPaper.ClassicalFourthData.Bq 884
    have hp : val WuPaper.ClassicalFourthData.Bq 884 = (89901033376213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 884 = 89901033376213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 884 = (2221:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 885) ≤ val WuPaper.ClassicalFourthData.Bq 885
    have hp : val WuPaper.ClassicalFourthData.Bq 885 = (89983083567746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 885 = 89983083567746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 885 = (1777:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 886) ≤ val WuPaper.ClassicalFourthData.Bq 886
    have hp : val WuPaper.ClassicalFourthData.Bq 886 = (90065096428386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 886 = 90065096428386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 886 = (4443:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 887) ≤ val WuPaper.ClassicalFourthData.Bq 887
    have hp : val WuPaper.ClassicalFourthData.Bq 887 = (90147071978453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 887 = 90147071978453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 887 = (8887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_887
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 888) ≤ val WuPaper.ClassicalFourthData.Bq 888
    have hp : val WuPaper.ClassicalFourthData.Bq 888 = (90229010238256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 888 = 90229010238256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 888 = (1111:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 889) ≤ val WuPaper.ClassicalFourthData.Bq 889
    have hp : val WuPaper.ClassicalFourthData.Bq 889 = (90310911228088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 889 = 90310911228088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 889 = (8889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 890) ≤ val WuPaper.ClassicalFourthData.Bq 890
    have hp : val WuPaper.ClassicalFourthData.Bq 890 = (90392774968230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 890 = 90392774968230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 890 = (889:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 891) ≤ val WuPaper.ClassicalFourthData.Bq 891
    have hp : val WuPaper.ClassicalFourthData.Bq 891 = (90474601478948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 891 = 90474601478948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 891 = (8891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 892) ≤ val WuPaper.ClassicalFourthData.Bq 892
    have hp : val WuPaper.ClassicalFourthData.Bq 892 = (90556390780493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 892 = 90556390780493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 892 = (2223:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 893) ≤ val WuPaper.ClassicalFourthData.Bq 893
    have hp : val WuPaper.ClassicalFourthData.Bq 893 = (90638142893106:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 893 = 90638142893106 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 893 = (8893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 894) ≤ val WuPaper.ClassicalFourthData.Bq 894
    have hp : val WuPaper.ClassicalFourthData.Bq 894 = (90719857837009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 894 = 90719857837009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 894 = (4447:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 895) ≤ val WuPaper.ClassicalFourthData.Bq 895
    have hp : val WuPaper.ClassicalFourthData.Bq 895 = (90801535632416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 895 = 90801535632416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 895 = (1779:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_055
