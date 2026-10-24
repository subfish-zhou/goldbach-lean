import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints444
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_444 (j : Fin 16) (hj : 16*444+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*444+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*444+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7104) ≤ val WuPaper.ClassicalFourthData.Bq 7104
    have hp : val WuPaper.ClassicalFourthData.Bq 7104 = (270394873581804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7104 = 270394873581804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7104 = (472:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7105) ≤ val WuPaper.ClassicalFourthData.Bq 7105
    have hp : val WuPaper.ClassicalFourthData.Bq 7105 = (270400819921042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7105 = 270400819921042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7105 = (3021:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7106) ≤ val WuPaper.ClassicalFourthData.Bq 7106
    have hp : val WuPaper.ClassicalFourthData.Bq 7106 = (270406763325794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7106 = 270406763325794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7106 = (7553:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7107) ≤ val WuPaper.ClassicalFourthData.Bq 7107
    have hp : val WuPaper.ClassicalFourthData.Bq 7107 = (270412703797029:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7107 = 270412703797029 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7107 = (15107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7108) ≤ val WuPaper.ClassicalFourthData.Bq 7108
    have hp : val WuPaper.ClassicalFourthData.Bq 7108 = (270418641335716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7108 = 270418641335716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7108 = (3777:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7109) ≤ val WuPaper.ClassicalFourthData.Bq 7109
    have hp : val WuPaper.ClassicalFourthData.Bq 7109 = (270424575942824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7109 = 270424575942824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7109 = (15109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7110) ≤ val WuPaper.ClassicalFourthData.Bq 7110
    have hp : val WuPaper.ClassicalFourthData.Bq 7110 = (270430507619322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7110 = 270430507619322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7110 = (1511:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7111) ≤ val WuPaper.ClassicalFourthData.Bq 7111
    have hp : val WuPaper.ClassicalFourthData.Bq 7111 = (270436436366176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7111 = 270436436366176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7111 = (15111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7111
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7112) ≤ val WuPaper.ClassicalFourthData.Bq 7112
    have hp : val WuPaper.ClassicalFourthData.Bq 7112 = (270442362184355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7112 = 270442362184355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7112 = (1889:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7113) ≤ val WuPaper.ClassicalFourthData.Bq 7113
    have hp : val WuPaper.ClassicalFourthData.Bq 7113 = (270448285074826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7113 = 270448285074826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7113 = (15113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7114) ≤ val WuPaper.ClassicalFourthData.Bq 7114
    have hp : val WuPaper.ClassicalFourthData.Bq 7114 = (270454205038555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7114 = 270454205038555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7114 = (7557:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7115) ≤ val WuPaper.ClassicalFourthData.Bq 7115
    have hp : val WuPaper.ClassicalFourthData.Bq 7115 = (270460122076510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7115 = 270460122076510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7115 = (3023:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7116) ≤ val WuPaper.ClassicalFourthData.Bq 7116
    have hp : val WuPaper.ClassicalFourthData.Bq 7116 = (270466036189656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7116 = 270466036189656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7116 = (3779:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7117) ≤ val WuPaper.ClassicalFourthData.Bq 7117
    have hp : val WuPaper.ClassicalFourthData.Bq 7117 = (270471947378959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7117 = 270471947378959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7117 = (15117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7118) ≤ val WuPaper.ClassicalFourthData.Bq 7118
    have hp : val WuPaper.ClassicalFourthData.Bq 7118 = (270477855645385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7118 = 270477855645385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7118 = (7559:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7119) ≤ val WuPaper.ClassicalFourthData.Bq 7119
    have hp : val WuPaper.ClassicalFourthData.Bq 7119 = (270483760989898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7119 = 270483760989898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7119 = (15119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_444
