import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints189
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_189 (j : Fin 16) (hj : 16*189+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*189+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*189+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3024) ≤ val WuPaper.ClassicalFourthData.Bq 3024
    have hp : val WuPaper.ClassicalFourthData.Bq 3024 = (204295535273195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3024 = 204295535273195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3024 = (689:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3025) ≤ val WuPaper.ClassicalFourthData.Bq 3025
    have hp : val WuPaper.ClassicalFourthData.Bq 3025 = (204328654548724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3025 = 204328654548724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3025 = (441:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3026) ≤ val WuPaper.ClassicalFourthData.Bq 3026
    have hp : val WuPaper.ClassicalFourthData.Bq 3026 = (204361760465716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3026 = 204361760465716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3026 = (5513:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3027) ≤ val WuPaper.ClassicalFourthData.Bq 3027
    have hp : val WuPaper.ClassicalFourthData.Bq 3027 = (204394853029898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3027 = 204394853029898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3027 = (11027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3028) ≤ val WuPaper.ClassicalFourthData.Bq 3028
    have hp : val WuPaper.ClassicalFourthData.Bq 3028 = (204427932246994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3028 = 204427932246994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3028 = (2757:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3029) ≤ val WuPaper.ClassicalFourthData.Bq 3029
    have hp : val WuPaper.ClassicalFourthData.Bq 3029 = (204460998122723:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3029 = 204460998122723 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3029 = (11029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3030) ≤ val WuPaper.ClassicalFourthData.Bq 3030
    have hp : val WuPaper.ClassicalFourthData.Bq 3030 = (204494050662805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3030 = 204494050662805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3030 = (1103:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3031) ≤ val WuPaper.ClassicalFourthData.Bq 3031
    have hp : val WuPaper.ClassicalFourthData.Bq 3031 = (204527089872953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3031 = 204527089872953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3031 = (11031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3031
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3032) ≤ val WuPaper.ClassicalFourthData.Bq 3032
    have hp : val WuPaper.ClassicalFourthData.Bq 3032 = (204560115758878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3032 = 204560115758878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3032 = (1379:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3033) ≤ val WuPaper.ClassicalFourthData.Bq 3033
    have hp : val WuPaper.ClassicalFourthData.Bq 3033 = (204593128326291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3033 = 204593128326291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3033 = (11033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3034) ≤ val WuPaper.ClassicalFourthData.Bq 3034
    have hp : val WuPaper.ClassicalFourthData.Bq 3034 = (204626127580896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3034 = 204626127580896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3034 = (5517:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3035) ≤ val WuPaper.ClassicalFourthData.Bq 3035
    have hp : val WuPaper.ClassicalFourthData.Bq 3035 = (204659113528396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3035 = 204659113528396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3035 = (2207:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3036) ≤ val WuPaper.ClassicalFourthData.Bq 3036
    have hp : val WuPaper.ClassicalFourthData.Bq 3036 = (204692086174492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3036 = 204692086174492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3036 = (2759:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3037) ≤ val WuPaper.ClassicalFourthData.Bq 3037
    have hp : val WuPaper.ClassicalFourthData.Bq 3037 = (204725045524879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3037 = 204725045524879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3037 = (11037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3038) ≤ val WuPaper.ClassicalFourthData.Bq 3038
    have hp : val WuPaper.ClassicalFourthData.Bq 3038 = (204757991585252:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3038 = 204757991585252 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3038 = (5519:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3039) ≤ val WuPaper.ClassicalFourthData.Bq 3039
    have hp : val WuPaper.ClassicalFourthData.Bq 3039 = (204790924361303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3039 = 204790924361303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3039 = (11039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_189
