import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints008
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_008 (j : Fin 16) (hj : 16*8+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*8+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*8+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 128) ≤ val WuPaper.ClassicalFourthData.Bq 128
    have hp : val WuPaper.ClassicalFourthData.Bq 128 = (15501312529219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 128 = 15501312529219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 128 = (254:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 129) ≤ val WuPaper.ClassicalFourthData.Bq 129
    have hp : val WuPaper.ClassicalFourthData.Bq 129 = (15618593078639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 129 = 15618593078639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 129 = (8129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 130) ≤ val WuPaper.ClassicalFourthData.Bq 130
    have hp : val WuPaper.ClassicalFourthData.Bq 130 = (15735815917861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 130 = 15735815917861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 130 = (813:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 131) ≤ val WuPaper.ClassicalFourthData.Bq 131
    have hp : val WuPaper.ClassicalFourthData.Bq 131 = (15852981082149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 131 = 15852981082149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 131 = (8131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 132) ≤ val WuPaper.ClassicalFourthData.Bq 132
    have hp : val WuPaper.ClassicalFourthData.Bq 132 = (15970088606740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 132 = 15970088606740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 132 = (2033:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 133) ≤ val WuPaper.ClassicalFourthData.Bq 133
    have hp : val WuPaper.ClassicalFourthData.Bq 133 = (16087138526844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 133 = 16087138526844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 133 = (8133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 134) ≤ val WuPaper.ClassicalFourthData.Bq 134
    have hp : val WuPaper.ClassicalFourthData.Bq 134 = (16204130877643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 134 = 16204130877643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 134 = (4067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 135) ≤ val WuPaper.ClassicalFourthData.Bq 135
    have hp : val WuPaper.ClassicalFourthData.Bq 135 = (16321065694291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 135 = 16321065694291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 135 = (1627:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 136) ≤ val WuPaper.ClassicalFourthData.Bq 136
    have hp : val WuPaper.ClassicalFourthData.Bq 136 = (16437943011917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 136 = 16437943011917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 136 = (1017:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 137) ≤ val WuPaper.ClassicalFourthData.Bq 137
    have hp : val WuPaper.ClassicalFourthData.Bq 137 = (16554762865619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 137 = 16554762865619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 137 = (8137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 138) ≤ val WuPaper.ClassicalFourthData.Bq 138
    have hp : val WuPaper.ClassicalFourthData.Bq 138 = (16671525290470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 138 = 16671525290470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 138 = (4069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 139) ≤ val WuPaper.ClassicalFourthData.Bq 139
    have hp : val WuPaper.ClassicalFourthData.Bq 139 = (16788230321517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 139 = 16788230321517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 139 = (8139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 140) ≤ val WuPaper.ClassicalFourthData.Bq 140
    have hp : val WuPaper.ClassicalFourthData.Bq 140 = (16904877993776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 140 = 16904877993776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 140 = (407:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 141) ≤ val WuPaper.ClassicalFourthData.Bq 141
    have hp : val WuPaper.ClassicalFourthData.Bq 141 = (17021468342238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 141 = 17021468342238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 141 = (8141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 142) ≤ val WuPaper.ClassicalFourthData.Bq 142
    have hp : val WuPaper.ClassicalFourthData.Bq 142 = (17138001401868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 142 = 17138001401868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 142 = (4071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 143) ≤ val WuPaper.ClassicalFourthData.Bq 143
    have hp : val WuPaper.ClassicalFourthData.Bq 143 = (17254477207602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 143 = 17254477207602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 143 = (8143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_008
