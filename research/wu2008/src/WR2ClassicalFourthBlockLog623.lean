import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints623
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_623 (j : Fin 16) (hj : 16*623+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*623+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*623+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9968) ≤ val WuPaper.ClassicalFourthData.Bq 9968
    have hp : val WuPaper.ClassicalFourthData.Bq 9968 = (278378147388230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9968 = 278378147388230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9968 = (1123:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9969) ≤ val WuPaper.ClassicalFourthData.Bq 9969
    have hp : val WuPaper.ClassicalFourthData.Bq 9969 = (278378591511211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9969 = 278378591511211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9969 = (17969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9970) ≤ val WuPaper.ClassicalFourthData.Bq 9970
    have hp : val WuPaper.ClassicalFourthData.Bq 9970 = (278379034444037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9970 = 278379034444037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9970 = (1797:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9971) ≤ val WuPaper.ClassicalFourthData.Bq 9971
    have hp : val WuPaper.ClassicalFourthData.Bq 9971 = (278379476187070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9971 = 278379476187070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9971 = (17971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9972) ≤ val WuPaper.ClassicalFourthData.Bq 9972
    have hp : val WuPaper.ClassicalFourthData.Bq 9972 = (278379916740672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9972 = 278379916740672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9972 = (4493:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9973) ≤ val WuPaper.ClassicalFourthData.Bq 9973
    have hp : val WuPaper.ClassicalFourthData.Bq 9973 = (278380356105204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9973 = 278380356105204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9973 = (17973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9974) ≤ val WuPaper.ClassicalFourthData.Bq 9974
    have hp : val WuPaper.ClassicalFourthData.Bq 9974 = (278380794281028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9974 = 278380794281028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9974 = (8987:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9975) ≤ val WuPaper.ClassicalFourthData.Bq 9975
    have hp : val WuPaper.ClassicalFourthData.Bq 9975 = (278381231268505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9975 = 278381231268505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9975 = (719:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9975
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9976) ≤ val WuPaper.ClassicalFourthData.Bq 9976
    have hp : val WuPaper.ClassicalFourthData.Bq 9976 = (278381667067997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9976 = 278381667067997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9976 = (2247:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9977) ≤ val WuPaper.ClassicalFourthData.Bq 9977
    have hp : val WuPaper.ClassicalFourthData.Bq 9977 = (278382101679866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9977 = 278382101679866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9977 = (17977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9978) ≤ val WuPaper.ClassicalFourthData.Bq 9978
    have hp : val WuPaper.ClassicalFourthData.Bq 9978 = (278382535104472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9978 = 278382535104472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9978 = (8989:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9979) ≤ val WuPaper.ClassicalFourthData.Bq 9979
    have hp : val WuPaper.ClassicalFourthData.Bq 9979 = (278382967342177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9979 = 278382967342177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9979 = (17979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9980) ≤ val WuPaper.ClassicalFourthData.Bq 9980
    have hp : val WuPaper.ClassicalFourthData.Bq 9980 = (278383398393340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9980 = 278383398393340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9980 = (899:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9981) ≤ val WuPaper.ClassicalFourthData.Bq 9981
    have hp : val WuPaper.ClassicalFourthData.Bq 9981 = (278383828258324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9981 = 278383828258324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9981 = (17981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9982) ≤ val WuPaper.ClassicalFourthData.Bq 9982
    have hp : val WuPaper.ClassicalFourthData.Bq 9982 = (278384256937489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9982 = 278384256937489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9982 = (8991:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9983) ≤ val WuPaper.ClassicalFourthData.Bq 9983
    have hp : val WuPaper.ClassicalFourthData.Bq 9983 = (278384684431196:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9983 = 278384684431196 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9983 = (17983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_623
