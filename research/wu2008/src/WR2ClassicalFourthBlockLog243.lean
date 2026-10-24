import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints243
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_243 (j : Fin 16) (hj : 16*243+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*243+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*243+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3888) ≤ val WuPaper.ClassicalFourthData.Bq 3888
    have hp : val WuPaper.ClassicalFourthData.Bq 3888 = (228481916615224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3888 = 228481916615224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3888 = (743:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3889) ≤ val WuPaper.ClassicalFourthData.Bq 3889
    have hp : val WuPaper.ClassicalFourthData.Bq 3889 = (228505348807490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3889 = 228505348807490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3889 = (11889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3890) ≤ val WuPaper.ClassicalFourthData.Bq 3890
    have hp : val WuPaper.ClassicalFourthData.Bq 3890 = (228528771652782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3890 = 228528771652782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3890 = (1189:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3891) ≤ val WuPaper.ClassicalFourthData.Bq 3891
    have hp : val WuPaper.ClassicalFourthData.Bq 3891 = (228552185154826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3891 = 228552185154826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3891 = (11891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3892) ≤ val WuPaper.ClassicalFourthData.Bq 3892
    have hp : val WuPaper.ClassicalFourthData.Bq 3892 = (228575589317349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3892 = 228575589317349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3892 = (2973:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3893) ≤ val WuPaper.ClassicalFourthData.Bq 3893
    have hp : val WuPaper.ClassicalFourthData.Bq 3893 = (228598984144077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3893 = 228598984144077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3893 = (11893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3894) ≤ val WuPaper.ClassicalFourthData.Bq 3894
    have hp : val WuPaper.ClassicalFourthData.Bq 3894 = (228622369638731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3894 = 228622369638731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3894 = (5947:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3895) ≤ val WuPaper.ClassicalFourthData.Bq 3895
    have hp : val WuPaper.ClassicalFourthData.Bq 3895 = (228645745805033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3895 = 228645745805033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3895 = (2379:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3895
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3896) ≤ val WuPaper.ClassicalFourthData.Bq 3896
    have hp : val WuPaper.ClassicalFourthData.Bq 3896 = (228669112646702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3896 = 228669112646702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3896 = (1487:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3897) ≤ val WuPaper.ClassicalFourthData.Bq 3897
    have hp : val WuPaper.ClassicalFourthData.Bq 3897 = (228692470167456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3897 = 228692470167456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3897 = (11897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3898) ≤ val WuPaper.ClassicalFourthData.Bq 3898
    have hp : val WuPaper.ClassicalFourthData.Bq 3898 = (228715818371010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3898 = 228715818371010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3898 = (5949:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3899) ≤ val WuPaper.ClassicalFourthData.Bq 3899
    have hp : val WuPaper.ClassicalFourthData.Bq 3899 = (228739157261078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3899 = 228739157261078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3899 = (11899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3900) ≤ val WuPaper.ClassicalFourthData.Bq 3900
    have hp : val WuPaper.ClassicalFourthData.Bq 3900 = (228762486841374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3900 = 228762486841374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3900 = (119:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3901) ≤ val WuPaper.ClassicalFourthData.Bq 3901
    have hp : val WuPaper.ClassicalFourthData.Bq 3901 = (228785807115606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3901 = 228785807115606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3901 = (11901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3902) ≤ val WuPaper.ClassicalFourthData.Bq 3902
    have hp : val WuPaper.ClassicalFourthData.Bq 3902 = (228809118087484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3902 = 228809118087484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3902 = (5951:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3903) ≤ val WuPaper.ClassicalFourthData.Bq 3903
    have hp : val WuPaper.ClassicalFourthData.Bq 3903 = (228832419760715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3903 = 228832419760715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3903 = (11903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_243
