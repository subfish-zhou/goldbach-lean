import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints492
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_492 (j : Fin 16) (hj : 16*492+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*492+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*492+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7872) ≤ val WuPaper.ClassicalFourthData.Bq 7872
    have hp : val WuPaper.ClassicalFourthData.Bq 7872 = (274165404563276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7872 = 274165404563276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7872 = (496:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7873) ≤ val WuPaper.ClassicalFourthData.Bq 7873
    have hp : val WuPaper.ClassicalFourthData.Bq 7873 = (274169357667917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7873 = 274169357667917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7873 = (15873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7874) ≤ val WuPaper.ClassicalFourthData.Bq 7874
    have hp : val WuPaper.ClassicalFourthData.Bq 7874 = (274173308486971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7874 = 274173308486971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7874 = (7937:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7875) ≤ val WuPaper.ClassicalFourthData.Bq 7875
    have hp : val WuPaper.ClassicalFourthData.Bq 7875 = (274177257021171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7875 = 274177257021171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7875 = (127:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7876) ≤ val WuPaper.ClassicalFourthData.Bq 7876
    have hp : val WuPaper.ClassicalFourthData.Bq 7876 = (274181203271248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7876 = 274181203271248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7876 = (3969:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7877) ≤ val WuPaper.ClassicalFourthData.Bq 7877
    have hp : val WuPaper.ClassicalFourthData.Bq 7877 = (274185147237936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7877 = 274185147237936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7877 = (15877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7878) ≤ val WuPaper.ClassicalFourthData.Bq 7878
    have hp : val WuPaper.ClassicalFourthData.Bq 7878 = (274189088921967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7878 = 274189088921967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7878 = (7939:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7879) ≤ val WuPaper.ClassicalFourthData.Bq 7879
    have hp : val WuPaper.ClassicalFourthData.Bq 7879 = (274193028324072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7879 = 274193028324072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7879 = (15879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7879
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7880) ≤ val WuPaper.ClassicalFourthData.Bq 7880
    have hp : val WuPaper.ClassicalFourthData.Bq 7880 = (274196965444984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7880 = 274196965444984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7880 = (397:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7881) ≤ val WuPaper.ClassicalFourthData.Bq 7881
    have hp : val WuPaper.ClassicalFourthData.Bq 7881 = (274200900285433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7881 = 274200900285433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7881 = (15881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7882) ≤ val WuPaper.ClassicalFourthData.Bq 7882
    have hp : val WuPaper.ClassicalFourthData.Bq 7882 = (274204832846152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7882 = 274204832846152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7882 = (7941:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7883) ≤ val WuPaper.ClassicalFourthData.Bq 7883
    have hp : val WuPaper.ClassicalFourthData.Bq 7883 = (274208763127870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7883 = 274208763127870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7883 = (15883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7884) ≤ val WuPaper.ClassicalFourthData.Bq 7884
    have hp : val WuPaper.ClassicalFourthData.Bq 7884 = (274212691131319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7884 = 274212691131319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7884 = (3971:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7885) ≤ val WuPaper.ClassicalFourthData.Bq 7885
    have hp : val WuPaper.ClassicalFourthData.Bq 7885 = (274216616857228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7885 = 274216616857228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7885 = (3177:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7886) ≤ val WuPaper.ClassicalFourthData.Bq 7886
    have hp : val WuPaper.ClassicalFourthData.Bq 7886 = (274220540306328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7886 = 274220540306328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7886 = (7943:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7887) ≤ val WuPaper.ClassicalFourthData.Bq 7887
    have hp : val WuPaper.ClassicalFourthData.Bq 7887 = (274224461479349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7887 = 274224461479349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7887 = (15887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_492
