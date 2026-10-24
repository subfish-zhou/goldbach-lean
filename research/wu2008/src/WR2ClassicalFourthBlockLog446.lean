import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints446
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_446 (j : Fin 16) (hj : 16*446+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*446+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*446+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7136) ≤ val WuPaper.ClassicalFourthData.Bq 7136
    have hp : val WuPaper.ClassicalFourthData.Bq 7136 = (270583705727414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7136 = 270583705727414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7136 = (473:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7137) ≤ val WuPaper.ClassicalFourthData.Bq 7137
    have hp : val WuPaper.ClassicalFourthData.Bq 7137 = (270589558642118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7137 = 270589558642118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7137 = (15137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7138) ≤ val WuPaper.ClassicalFourthData.Bq 7138
    have hp : val WuPaper.ClassicalFourthData.Bq 7138 = (270595408653177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7138 = 270595408653177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7138 = (7569:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7139) ≤ val WuPaper.ClassicalFourthData.Bq 7139
    have hp : val WuPaper.ClassicalFourthData.Bq 7139 = (270601255761550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7139 = 270601255761550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7139 = (15139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7140) ≤ val WuPaper.ClassicalFourthData.Bq 7140
    have hp : val WuPaper.ClassicalFourthData.Bq 7140 = (270607099968194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7140 = 270607099968194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7140 = (757:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7141) ≤ val WuPaper.ClassicalFourthData.Bq 7141
    have hp : val WuPaper.ClassicalFourthData.Bq 7141 = (270612941274065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7141 = 270612941274065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7141 = (15141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7142) ≤ val WuPaper.ClassicalFourthData.Bq 7142
    have hp : val WuPaper.ClassicalFourthData.Bq 7142 = (270618779680122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7142 = 270618779680122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7142 = (7571:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7143) ≤ val WuPaper.ClassicalFourthData.Bq 7143
    have hp : val WuPaper.ClassicalFourthData.Bq 7143 = (270624615187319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7143 = 270624615187319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7143 = (15143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7143
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7144) ≤ val WuPaper.ClassicalFourthData.Bq 7144
    have hp : val WuPaper.ClassicalFourthData.Bq 7144 = (270630447796615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7144 = 270630447796615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7144 = (1893:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7145) ≤ val WuPaper.ClassicalFourthData.Bq 7145
    have hp : val WuPaper.ClassicalFourthData.Bq 7145 = (270636277508963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7145 = 270636277508963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7145 = (3029:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7146) ≤ val WuPaper.ClassicalFourthData.Bq 7146
    have hp : val WuPaper.ClassicalFourthData.Bq 7146 = (270642104325320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7146 = 270642104325320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7146 = (7573:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7147) ≤ val WuPaper.ClassicalFourthData.Bq 7147
    have hp : val WuPaper.ClassicalFourthData.Bq 7147 = (270647928246641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7147 = 270647928246641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7147 = (15147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7148) ≤ val WuPaper.ClassicalFourthData.Bq 7148
    have hp : val WuPaper.ClassicalFourthData.Bq 7148 = (270653749273880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7148 = 270653749273880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7148 = (3787:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7149) ≤ val WuPaper.ClassicalFourthData.Bq 7149
    have hp : val WuPaper.ClassicalFourthData.Bq 7149 = (270659567407992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7149 = 270659567407992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7149 = (15149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7150) ≤ val WuPaper.ClassicalFourthData.Bq 7150
    have hp : val WuPaper.ClassicalFourthData.Bq 7150 = (270665382649930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7150 = 270665382649930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7150 = (303:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7151) ≤ val WuPaper.ClassicalFourthData.Bq 7151
    have hp : val WuPaper.ClassicalFourthData.Bq 7151 = (270671195000649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7151 = 270671195000649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7151 = (15151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7151
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_446
