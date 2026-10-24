import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints305
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_305 (j : Fin 16) (hj : 16*305+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*305+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*305+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4880) ≤ val WuPaper.ClassicalFourthData.Bq 4880
    have hp : val WuPaper.ClassicalFourthData.Bq 4880 = (247673042200059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4880 = 247673042200059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4880 = (161:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4881) ≤ val WuPaper.ClassicalFourthData.Bq 4881
    have hp : val WuPaper.ClassicalFourthData.Bq 4881 = (247688782596531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4881 = 247688782596531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4881 = (12881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4882) ≤ val WuPaper.ClassicalFourthData.Bq 4882
    have hp : val WuPaper.ClassicalFourthData.Bq 4882 = (247704516612334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4882 = 247704516612334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4882 = (6441:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4883) ≤ val WuPaper.ClassicalFourthData.Bq 4883
    have hp : val WuPaper.ClassicalFourthData.Bq 4883 = (247720244249841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4883 = 247720244249841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4883 = (12883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4884) ≤ val WuPaper.ClassicalFourthData.Bq 4884
    have hp : val WuPaper.ClassicalFourthData.Bq 4884 = (247735965511423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4884 = 247735965511423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4884 = (3221:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4885) ≤ val WuPaper.ClassicalFourthData.Bq 4885
    have hp : val WuPaper.ClassicalFourthData.Bq 4885 = (247751680399449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4885 = 247751680399449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4885 = (2577:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4886) ≤ val WuPaper.ClassicalFourthData.Bq 4886
    have hp : val WuPaper.ClassicalFourthData.Bq 4886 = (247767388916290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4886 = 247767388916290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4886 = (6443:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4887) ≤ val WuPaper.ClassicalFourthData.Bq 4887
    have hp : val WuPaper.ClassicalFourthData.Bq 4887 = (247783091064313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4887 = 247783091064313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4887 = (12887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4887
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4888) ≤ val WuPaper.ClassicalFourthData.Bq 4888
    have hp : val WuPaper.ClassicalFourthData.Bq 4888 = (247798786845885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4888 = 247798786845885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4888 = (1611:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4889) ≤ val WuPaper.ClassicalFourthData.Bq 4889
    have hp : val WuPaper.ClassicalFourthData.Bq 4889 = (247814476263372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4889 = 247814476263372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4889 = (12889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4890) ≤ val WuPaper.ClassicalFourthData.Bq 4890
    have hp : val WuPaper.ClassicalFourthData.Bq 4890 = (247830159319139:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4890 = 247830159319139 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4890 = (1289:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4891) ≤ val WuPaper.ClassicalFourthData.Bq 4891
    have hp : val WuPaper.ClassicalFourthData.Bq 4891 = (247845836015550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4891 = 247845836015550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4891 = (12891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4892) ≤ val WuPaper.ClassicalFourthData.Bq 4892
    have hp : val WuPaper.ClassicalFourthData.Bq 4892 = (247861506354968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4892 = 247861506354968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4892 = (3223:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4893) ≤ val WuPaper.ClassicalFourthData.Bq 4893
    have hp : val WuPaper.ClassicalFourthData.Bq 4893 = (247877170339755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4893 = 247877170339755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4893 = (12893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4894) ≤ val WuPaper.ClassicalFourthData.Bq 4894
    have hp : val WuPaper.ClassicalFourthData.Bq 4894 = (247892827972271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4894 = 247892827972271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4894 = (6447:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4895) ≤ val WuPaper.ClassicalFourthData.Bq 4895
    have hp : val WuPaper.ClassicalFourthData.Bq 4895 = (247908479254877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4895 = 247908479254877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4895 = (2579:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4895
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_305
