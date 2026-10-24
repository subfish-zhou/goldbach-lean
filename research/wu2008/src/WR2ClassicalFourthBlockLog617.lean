import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints617
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_617 (j : Fin 16) (hj : 16*617+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*617+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*617+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9872) ≤ val WuPaper.ClassicalFourthData.Bq 9872
    have hp : val WuPaper.ClassicalFourthData.Bq 9872 = (278329914726084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9872 = 278329914726084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9872 = (1117:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9873) ≤ val WuPaper.ClassicalFourthData.Bq 9873
    have hp : val WuPaper.ClassicalFourthData.Bq 9873 = (278330474807066:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9873 = 278330474807066 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9873 = (17873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9874) ≤ val WuPaper.ClassicalFourthData.Bq 9874
    have hp : val WuPaper.ClassicalFourthData.Bq 9874 = (278331033662597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9874 = 278331033662597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9874 = (8937:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9875) ≤ val WuPaper.ClassicalFourthData.Bq 9875
    have hp : val WuPaper.ClassicalFourthData.Bq 9875 = (278331591293052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9875 = 278331591293052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9875 = (143:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9876) ≤ val WuPaper.ClassicalFourthData.Bq 9876
    have hp : val WuPaper.ClassicalFourthData.Bq 9876 = (278332147698805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9876 = 278332147698805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9876 = (4469:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9877) ≤ val WuPaper.ClassicalFourthData.Bq 9877
    have hp : val WuPaper.ClassicalFourthData.Bq 9877 = (278332702880226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9877 = 278332702880226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9877 = (17877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9878) ≤ val WuPaper.ClassicalFourthData.Bq 9878
    have hp : val WuPaper.ClassicalFourthData.Bq 9878 = (278333256837691:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9878 = 278333256837691 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9878 = (8939:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9879) ≤ val WuPaper.ClassicalFourthData.Bq 9879
    have hp : val WuPaper.ClassicalFourthData.Bq 9879 = (278333809571571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9879 = 278333809571571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9879 = (17879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9879
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9880) ≤ val WuPaper.ClassicalFourthData.Bq 9880
    have hp : val WuPaper.ClassicalFourthData.Bq 9880 = (278334361082240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9880 = 278334361082240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9880 = (447:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9881) ≤ val WuPaper.ClassicalFourthData.Bq 9881
    have hp : val WuPaper.ClassicalFourthData.Bq 9881 = (278334911370069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9881 = 278334911370069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9881 = (17881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9882) ≤ val WuPaper.ClassicalFourthData.Bq 9882
    have hp : val WuPaper.ClassicalFourthData.Bq 9882 = (278335460435431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9882 = 278335460435431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9882 = (8941:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9883) ≤ val WuPaper.ClassicalFourthData.Bq 9883
    have hp : val WuPaper.ClassicalFourthData.Bq 9883 = (278336008278699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9883 = 278336008278699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9883 = (17883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9884) ≤ val WuPaper.ClassicalFourthData.Bq 9884
    have hp : val WuPaper.ClassicalFourthData.Bq 9884 = (278336554900245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9884 = 278336554900245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9884 = (4471:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9885) ≤ val WuPaper.ClassicalFourthData.Bq 9885
    have hp : val WuPaper.ClassicalFourthData.Bq 9885 = (278337100300440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9885 = 278337100300440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9885 = (3577:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9886) ≤ val WuPaper.ClassicalFourthData.Bq 9886
    have hp : val WuPaper.ClassicalFourthData.Bq 9886 = (278337644479657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9886 = 278337644479657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9886 = (8943:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9887) ≤ val WuPaper.ClassicalFourthData.Bq 9887
    have hp : val WuPaper.ClassicalFourthData.Bq 9887 = (278338187438268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9887 = 278338187438268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9887 = (17887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_617
