import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints619
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_619 (j : Fin 16) (hj : 16*619+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*619+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*619+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9904) ≤ val WuPaper.ClassicalFourthData.Bq 9904
    have hp : val WuPaper.ClassicalFourthData.Bq 9904 = (278347231341609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9904 = 278347231341609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9904 = (1119:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9905) ≤ val WuPaper.ClassicalFourthData.Bq 9905
    have hp : val WuPaper.ClassicalFourthData.Bq 9905 = (278347752392754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9905 = 278347752392754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9905 = (3581:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9906) ≤ val WuPaper.ClassicalFourthData.Bq 9906
    have hp : val WuPaper.ClassicalFourthData.Bq 9906 = (278348272230334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9906 = 278348272230334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9906 = (8953:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9907) ≤ val WuPaper.ClassicalFourthData.Bq 9907
    have hp : val WuPaper.ClassicalFourthData.Bq 9907 = (278348790854720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9907 = 278348790854720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9907 = (17907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9908) ≤ val WuPaper.ClassicalFourthData.Bq 9908
    have hp : val WuPaper.ClassicalFourthData.Bq 9908 = (278349308266281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9908 = 278349308266281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9908 = (4477:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9909) ≤ val WuPaper.ClassicalFourthData.Bq 9909
    have hp : val WuPaper.ClassicalFourthData.Bq 9909 = (278349824465386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9909 = 278349824465386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9909 = (17909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9910) ≤ val WuPaper.ClassicalFourthData.Bq 9910
    have hp : val WuPaper.ClassicalFourthData.Bq 9910 = (278350339452404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9910 = 278350339452404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9910 = (1791:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9911) ≤ val WuPaper.ClassicalFourthData.Bq 9911
    have hp : val WuPaper.ClassicalFourthData.Bq 9911 = (278350853227704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9911 = 278350853227704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9911 = (17911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9911
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9912) ≤ val WuPaper.ClassicalFourthData.Bq 9912
    have hp : val WuPaper.ClassicalFourthData.Bq 9912 = (278351365791655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9912 = 278351365791655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9912 = (2239:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9913) ≤ val WuPaper.ClassicalFourthData.Bq 9913
    have hp : val WuPaper.ClassicalFourthData.Bq 9913 = (278351877144625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9913 = 278351877144625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9913 = (17913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9914) ≤ val WuPaper.ClassicalFourthData.Bq 9914
    have hp : val WuPaper.ClassicalFourthData.Bq 9914 = (278352387286984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9914 = 278352387286984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9914 = (8957:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9915) ≤ val WuPaper.ClassicalFourthData.Bq 9915
    have hp : val WuPaper.ClassicalFourthData.Bq 9915 = (278352896219100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9915 = 278352896219100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9915 = (3583:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9916) ≤ val WuPaper.ClassicalFourthData.Bq 9916
    have hp : val WuPaper.ClassicalFourthData.Bq 9916 = (278353403941341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9916 = 278353403941341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9916 = (4479:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9917) ≤ val WuPaper.ClassicalFourthData.Bq 9917
    have hp : val WuPaper.ClassicalFourthData.Bq 9917 = (278353910454076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9917 = 278353910454076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9917 = (17917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9918) ≤ val WuPaper.ClassicalFourthData.Bq 9918
    have hp : val WuPaper.ClassicalFourthData.Bq 9918 = (278354415757673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9918 = 278354415757673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9918 = (8959:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9919) ≤ val WuPaper.ClassicalFourthData.Bq 9919
    have hp : val WuPaper.ClassicalFourthData.Bq 9919 = (278354919852499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9919 = 278354919852499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9919 = (17919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_619
