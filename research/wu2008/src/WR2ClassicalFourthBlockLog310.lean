import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints310
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_310 (j : Fin 16) (hj : 16*310+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*310+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*310+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4960) ≤ val WuPaper.ClassicalFourthData.Bq 4960
    have hp : val WuPaper.ClassicalFourthData.Bq 4960 = (248912304279923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4960 = 248912304279923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4960 = (81:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4961) ≤ val WuPaper.ClassicalFourthData.Bq 4961
    have hp : val WuPaper.ClassicalFourthData.Bq 4961 = (248927541634810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4961 = 248927541634810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4961 = (12961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4962) ≤ val WuPaper.ClassicalFourthData.Bq 4962
    have hp : val WuPaper.ClassicalFourthData.Bq 4962 = (248942772795576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4962 = 248942772795576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4962 = (6481:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4963) ≤ val WuPaper.ClassicalFourthData.Bq 4963
    have hp : val WuPaper.ClassicalFourthData.Bq 4963 = (248957997764510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4963 = 248957997764510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4963 = (12963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4964) ≤ val WuPaper.ClassicalFourthData.Bq 4964
    have hp : val WuPaper.ClassicalFourthData.Bq 4964 = (248973216543904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4964 = 248973216543904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4964 = (3241:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4965) ≤ val WuPaper.ClassicalFourthData.Bq 4965
    have hp : val WuPaper.ClassicalFourthData.Bq 4965 = (248988429136046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4965 = 248988429136046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4965 = (2593:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4966) ≤ val WuPaper.ClassicalFourthData.Bq 4966
    have hp : val WuPaper.ClassicalFourthData.Bq 4966 = (249003635543224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4966 = 249003635543224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4966 = (6483:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4967) ≤ val WuPaper.ClassicalFourthData.Bq 4967
    have hp : val WuPaper.ClassicalFourthData.Bq 4967 = (249018835767725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4967 = 249018835767725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4967 = (12967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4967
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4968) ≤ val WuPaper.ClassicalFourthData.Bq 4968
    have hp : val WuPaper.ClassicalFourthData.Bq 4968 = (249034029811835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4968 = 249034029811835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4968 = (1621:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4969) ≤ val WuPaper.ClassicalFourthData.Bq 4969
    have hp : val WuPaper.ClassicalFourthData.Bq 4969 = (249049217677840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4969 = 249049217677840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4969 = (12969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4970) ≤ val WuPaper.ClassicalFourthData.Bq 4970
    have hp : val WuPaper.ClassicalFourthData.Bq 4970 = (249064399368024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4970 = 249064399368024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4970 = (1297:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4971) ≤ val WuPaper.ClassicalFourthData.Bq 4971
    have hp : val WuPaper.ClassicalFourthData.Bq 4971 = (249079574884668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4971 = 249079574884668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4971 = (12971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4972) ≤ val WuPaper.ClassicalFourthData.Bq 4972
    have hp : val WuPaper.ClassicalFourthData.Bq 4972 = (249094744230057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4972 = 249094744230057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4972 = (3243:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4973) ≤ val WuPaper.ClassicalFourthData.Bq 4973
    have hp : val WuPaper.ClassicalFourthData.Bq 4973 = (249109907406469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4973 = 249109907406469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4973 = (12973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4974) ≤ val WuPaper.ClassicalFourthData.Bq 4974
    have hp : val WuPaper.ClassicalFourthData.Bq 4974 = (249125064416187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4974 = 249125064416187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4974 = (6487:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4975) ≤ val WuPaper.ClassicalFourthData.Bq 4975
    have hp : val WuPaper.ClassicalFourthData.Bq 4975 = (249140215261489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4975 = 249140215261489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4975 = (519:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_310
