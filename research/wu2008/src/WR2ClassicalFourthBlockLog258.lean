import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints258
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_258 (j : Fin 16) (hj : 16*258+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*258+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*258+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4128) ≤ val WuPaper.ClassicalFourthData.Bq 4128
    have hp : val WuPaper.ClassicalFourthData.Bq 4128 = (233845821146516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4128 = 233845821146516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4128 = (379:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4129) ≤ val WuPaper.ClassicalFourthData.Bq 4129
    have hp : val WuPaper.ClassicalFourthData.Bq 4129 = (233867113082545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4129 = 233867113082545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4129 = (12129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4130) ≤ val WuPaper.ClassicalFourthData.Bq 4130
    have hp : val WuPaper.ClassicalFourthData.Bq 4130 = (233888396517669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4130 = 233888396517669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4130 = (1213:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4131) ≤ val WuPaper.ClassicalFourthData.Bq 4131
    have hp : val WuPaper.ClassicalFourthData.Bq 4131 = (233909671455218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4131 = 233909671455218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4131 = (12131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4132) ≤ val WuPaper.ClassicalFourthData.Bq 4132
    have hp : val WuPaper.ClassicalFourthData.Bq 4132 = (233930937898520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4132 = 233930937898520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4132 = (3033:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4133) ≤ val WuPaper.ClassicalFourthData.Bq 4133
    have hp : val WuPaper.ClassicalFourthData.Bq 4133 = (233952195850902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4133 = 233952195850902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4133 = (12133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4134) ≤ val WuPaper.ClassicalFourthData.Bq 4134
    have hp : val WuPaper.ClassicalFourthData.Bq 4134 = (233973445315689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4134 = 233973445315689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4134 = (6067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4135) ≤ val WuPaper.ClassicalFourthData.Bq 4135
    have hp : val WuPaper.ClassicalFourthData.Bq 4135 = (233994686296205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4135 = 233994686296205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4135 = (2427:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4136) ≤ val WuPaper.ClassicalFourthData.Bq 4136
    have hp : val WuPaper.ClassicalFourthData.Bq 4136 = (234015918795771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4136 = 234015918795771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4136 = (1517:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4137) ≤ val WuPaper.ClassicalFourthData.Bq 4137
    have hp : val WuPaper.ClassicalFourthData.Bq 4137 = (234037142817708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4137 = 234037142817708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4137 = (12137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4138) ≤ val WuPaper.ClassicalFourthData.Bq 4138
    have hp : val WuPaper.ClassicalFourthData.Bq 4138 = (234058358365335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4138 = 234058358365335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4138 = (6069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4139) ≤ val WuPaper.ClassicalFourthData.Bq 4139
    have hp : val WuPaper.ClassicalFourthData.Bq 4139 = (234079565441969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4139 = 234079565441969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4139 = (12139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4140) ≤ val WuPaper.ClassicalFourthData.Bq 4140
    have hp : val WuPaper.ClassicalFourthData.Bq 4140 = (234100764050926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4140 = 234100764050926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4140 = (607:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4141) ≤ val WuPaper.ClassicalFourthData.Bq 4141
    have hp : val WuPaper.ClassicalFourthData.Bq 4141 = (234121954195520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4141 = 234121954195520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4141 = (12141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4142) ≤ val WuPaper.ClassicalFourthData.Bq 4142
    have hp : val WuPaper.ClassicalFourthData.Bq 4142 = (234143135879064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4142 = 234143135879064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4142 = (6071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4143) ≤ val WuPaper.ClassicalFourthData.Bq 4143
    have hp : val WuPaper.ClassicalFourthData.Bq 4143 = (234164309104869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4143 = 234164309104869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4143 = (12143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_258
