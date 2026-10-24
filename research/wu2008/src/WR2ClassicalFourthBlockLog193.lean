import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints193
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_193 (j : Fin 16) (hj : 16*193+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*193+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*193+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3088) ≤ val WuPaper.ClassicalFourthData.Bq 3088
    have hp : val WuPaper.ClassicalFourthData.Bq 3088 = (206388474813453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3088 = 206388474813453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3088 = (693:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3089) ≤ val WuPaper.ClassicalFourthData.Bq 3089
    have hp : val WuPaper.ClassicalFourthData.Bq 3089 = (206420750564701:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3089 = 206420750564701 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3089 = (11089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3090) ≤ val WuPaper.ClassicalFourthData.Bq 3090
    have hp : val WuPaper.ClassicalFourthData.Bq 3090 = (206453013317997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3090 = 206453013317997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3090 = (1109:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3091) ≤ val WuPaper.ClassicalFourthData.Bq 3091
    have hp : val WuPaper.ClassicalFourthData.Bq 3091 = (206485263078882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3091 = 206485263078882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3091 = (11091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3092) ≤ val WuPaper.ClassicalFourthData.Bq 3092
    have hp : val WuPaper.ClassicalFourthData.Bq 3092 = (206517499852893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3092 = 206517499852893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3092 = (2773:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3093) ≤ val WuPaper.ClassicalFourthData.Bq 3093
    have hp : val WuPaper.ClassicalFourthData.Bq 3093 = (206549723645564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3093 = 206549723645564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3093 = (11093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3094) ≤ val WuPaper.ClassicalFourthData.Bq 3094
    have hp : val WuPaper.ClassicalFourthData.Bq 3094 = (206581934462427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3094 = 206581934462427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3094 = (5547:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3095) ≤ val WuPaper.ClassicalFourthData.Bq 3095
    have hp : val WuPaper.ClassicalFourthData.Bq 3095 = (206614132309010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3095 = 206614132309010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3095 = (2219:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3095
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3096) ≤ val WuPaper.ClassicalFourthData.Bq 3096
    have hp : val WuPaper.ClassicalFourthData.Bq 3096 = (206646317190840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3096 = 206646317190840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3096 = (1387:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3097) ≤ val WuPaper.ClassicalFourthData.Bq 3097
    have hp : val WuPaper.ClassicalFourthData.Bq 3097 = (206678489113438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3097 = 206678489113438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3097 = (11097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3098) ≤ val WuPaper.ClassicalFourthData.Bq 3098
    have hp : val WuPaper.ClassicalFourthData.Bq 3098 = (206710648082327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3098 = 206710648082327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3098 = (5549:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3099) ≤ val WuPaper.ClassicalFourthData.Bq 3099
    have hp : val WuPaper.ClassicalFourthData.Bq 3099 = (206742794103022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3099 = 206742794103022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3099 = (11099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3100) ≤ val WuPaper.ClassicalFourthData.Bq 3100
    have hp : val WuPaper.ClassicalFourthData.Bq 3100 = (206774927181038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3100 = 206774927181038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3100 = (111:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3101) ≤ val WuPaper.ClassicalFourthData.Bq 3101
    have hp : val WuPaper.ClassicalFourthData.Bq 3101 = (206807047321887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3101 = 206807047321887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3101 = (11101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3102) ≤ val WuPaper.ClassicalFourthData.Bq 3102
    have hp : val WuPaper.ClassicalFourthData.Bq 3102 = (206839154531078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3102 = 206839154531078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3102 = (5551:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3103) ≤ val WuPaper.ClassicalFourthData.Bq 3103
    have hp : val WuPaper.ClassicalFourthData.Bq 3103 = (206871248814116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3103 = 206871248814116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3103 = (11103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_193
