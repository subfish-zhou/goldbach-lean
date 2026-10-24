import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints257
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_257 (j : Fin 16) (hj : 16*257+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*257+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*257+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4112) ≤ val WuPaper.ClassicalFourthData.Bq 4112
    have hp : val WuPaper.ClassicalFourthData.Bq 4112 = (233503991323956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4112 = 233503991323956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4112 = (757:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4113) ≤ val WuPaper.ClassicalFourthData.Bq 4113
    have hp : val WuPaper.ClassicalFourthData.Bq 4113 = (233525419728569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4113 = 233525419728569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4113 = (12113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4114) ≤ val WuPaper.ClassicalFourthData.Bq 4114
    have hp : val WuPaper.ClassicalFourthData.Bq 4114 = (233546839578790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4114 = 233546839578790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4114 = (6057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4115) ≤ val WuPaper.ClassicalFourthData.Bq 4115
    have hp : val WuPaper.ClassicalFourthData.Bq 4115 = (233568250877975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4115 = 233568250877975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4115 = (2423:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4116) ≤ val WuPaper.ClassicalFourthData.Bq 4116
    have hp : val WuPaper.ClassicalFourthData.Bq 4116 = (233589653629475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4116 = 233589653629475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4116 = (3029:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4117) ≤ val WuPaper.ClassicalFourthData.Bq 4117
    have hp : val WuPaper.ClassicalFourthData.Bq 4117 = (233611047836643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4117 = 233611047836643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4117 = (12117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4118) ≤ val WuPaper.ClassicalFourthData.Bq 4118
    have hp : val WuPaper.ClassicalFourthData.Bq 4118 = (233632433502828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4118 = 233632433502828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4118 = (6059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4119) ≤ val WuPaper.ClassicalFourthData.Bq 4119
    have hp : val WuPaper.ClassicalFourthData.Bq 4119 = (233653810631379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4119 = 233653810631379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4119 = (12119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4120) ≤ val WuPaper.ClassicalFourthData.Bq 4120
    have hp : val WuPaper.ClassicalFourthData.Bq 4120 = (233675179225643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4120 = 233675179225643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4120 = (303:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4121) ≤ val WuPaper.ClassicalFourthData.Bq 4121
    have hp : val WuPaper.ClassicalFourthData.Bq 4121 = (233696539288965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4121 = 233696539288965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4121 = (12121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4122) ≤ val WuPaper.ClassicalFourthData.Bq 4122
    have hp : val WuPaper.ClassicalFourthData.Bq 4122 = (233717890824688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4122 = 233717890824688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4122 = (6061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4123) ≤ val WuPaper.ClassicalFourthData.Bq 4123
    have hp : val WuPaper.ClassicalFourthData.Bq 4123 = (233739233836155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4123 = 233739233836155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4123 = (12123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4124) ≤ val WuPaper.ClassicalFourthData.Bq 4124
    have hp : val WuPaper.ClassicalFourthData.Bq 4124 = (233760568326707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4124 = 233760568326707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4124 = (3031:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4125) ≤ val WuPaper.ClassicalFourthData.Bq 4125
    have hp : val WuPaper.ClassicalFourthData.Bq 4125 = (233781894299682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4125 = 233781894299682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4125 = (97:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4126) ≤ val WuPaper.ClassicalFourthData.Bq 4126
    have hp : val WuPaper.ClassicalFourthData.Bq 4126 = (233803211758419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4126 = 233803211758419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4126 = (6063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4127) ≤ val WuPaper.ClassicalFourthData.Bq 4127
    have hp : val WuPaper.ClassicalFourthData.Bq 4127 = (233824520706252:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4127 = 233824520706252 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4127 = (12127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_257
