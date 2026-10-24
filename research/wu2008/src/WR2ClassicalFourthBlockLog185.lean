import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints185
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_185 (j : Fin 16) (hj : 16*185+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*185+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*185+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2960) ≤ val WuPaper.ClassicalFourthData.Bq 2960
    have hp : val WuPaper.ClassicalFourthData.Bq 2960 = (202147851542496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2960 = 202147851542496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2960 = (137:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2961) ≤ val WuPaper.ClassicalFourthData.Bq 2961
    have hp : val WuPaper.ClassicalFourthData.Bq 2961 = (202181837812842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2961 = 202181837812842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2961 = (10961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2962) ≤ val WuPaper.ClassicalFourthData.Bq 2962
    have hp : val WuPaper.ClassicalFourthData.Bq 2962 = (202215810351891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2962 = 202215810351891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2962 = (5481:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2963) ≤ val WuPaper.ClassicalFourthData.Bq 2963
    have hp : val WuPaper.ClassicalFourthData.Bq 2963 = (202249769165564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2963 = 202249769165564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2963 = (10963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2964) ≤ val WuPaper.ClassicalFourthData.Bq 2964
    have hp : val WuPaper.ClassicalFourthData.Bq 2964 = (202283714259779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2964 = 202283714259779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2964 = (2741:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2965) ≤ val WuPaper.ClassicalFourthData.Bq 2965
    have hp : val WuPaper.ClassicalFourthData.Bq 2965 = (202317645640449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2965 = 202317645640449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2965 = (2193:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2966) ≤ val WuPaper.ClassicalFourthData.Bq 2966
    have hp : val WuPaper.ClassicalFourthData.Bq 2966 = (202351563313485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2966 = 202351563313485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2966 = (5483:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2967) ≤ val WuPaper.ClassicalFourthData.Bq 2967
    have hp : val WuPaper.ClassicalFourthData.Bq 2967 = (202385467284797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2967 = 202385467284797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2967 = (10967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2967
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2968) ≤ val WuPaper.ClassicalFourthData.Bq 2968
    have hp : val WuPaper.ClassicalFourthData.Bq 2968 = (202419357560289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2968 = 202419357560289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2968 = (1371:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2969) ≤ val WuPaper.ClassicalFourthData.Bq 2969
    have hp : val WuPaper.ClassicalFourthData.Bq 2969 = (202453234145863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2969 = 202453234145863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2969 = (10969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2970) ≤ val WuPaper.ClassicalFourthData.Bq 2970
    have hp : val WuPaper.ClassicalFourthData.Bq 2970 = (202487097047418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2970 = 202487097047418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2970 = (1097:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2971) ≤ val WuPaper.ClassicalFourthData.Bq 2971
    have hp : val WuPaper.ClassicalFourthData.Bq 2971 = (202520946270849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2971 = 202520946270849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2971 = (10971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2972) ≤ val WuPaper.ClassicalFourthData.Bq 2972
    have hp : val WuPaper.ClassicalFourthData.Bq 2972 = (202554781822051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2972 = 202554781822051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2972 = (2743:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2973) ≤ val WuPaper.ClassicalFourthData.Bq 2973
    have hp : val WuPaper.ClassicalFourthData.Bq 2973 = (202588603706911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2973 = 202588603706911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2973 = (10973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2974) ≤ val WuPaper.ClassicalFourthData.Bq 2974
    have hp : val WuPaper.ClassicalFourthData.Bq 2974 = (202622411931318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2974 = 202622411931318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2974 = (5487:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2975) ≤ val WuPaper.ClassicalFourthData.Bq 2975
    have hp : val WuPaper.ClassicalFourthData.Bq 2975 = (202656206501154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2975 = 202656206501154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2975 = (439:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_185
