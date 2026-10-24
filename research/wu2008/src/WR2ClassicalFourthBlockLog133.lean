import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints133
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_133 (j : Fin 16) (hj : 16*133+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*133+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*133+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2128) ≤ val WuPaper.ClassicalFourthData.Bq 2128
    have hp : val WuPaper.ClassicalFourthData.Bq 2128 = (168473171926699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2128 = 168473171926699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2128 = (633:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2129) ≤ val WuPaper.ClassicalFourthData.Bq 2129
    have hp : val WuPaper.ClassicalFourthData.Bq 2129 = (168520976753364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2129 = 168520976753364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2129 = (10129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2130) ≤ val WuPaper.ClassicalFourthData.Bq 2130
    have hp : val WuPaper.ClassicalFourthData.Bq 2130 = (168568761630101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2130 = 168568761630101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2130 = (1013:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2131) ≤ val WuPaper.ClassicalFourthData.Bq 2131
    have hp : val WuPaper.ClassicalFourthData.Bq 2131 = (168616526566247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2131 = 168616526566247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2131 = (10131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2132) ≤ val WuPaper.ClassicalFourthData.Bq 2132
    have hp : val WuPaper.ClassicalFourthData.Bq 2132 = (168664271571132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2132 = 168664271571132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2132 = (2533:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2133) ≤ val WuPaper.ClassicalFourthData.Bq 2133
    have hp : val WuPaper.ClassicalFourthData.Bq 2133 = (168711996654084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2133 = 168711996654084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2133 = (10133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2134) ≤ val WuPaper.ClassicalFourthData.Bq 2134
    have hp : val WuPaper.ClassicalFourthData.Bq 2134 = (168759701824421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2134 = 168759701824421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2134 = (5067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2135) ≤ val WuPaper.ClassicalFourthData.Bq 2135
    have hp : val WuPaper.ClassicalFourthData.Bq 2135 = (168807387091459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2135 = 168807387091459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2135 = (2027:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2136) ≤ val WuPaper.ClassicalFourthData.Bq 2136
    have hp : val WuPaper.ClassicalFourthData.Bq 2136 = (168855052464509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2136 = 168855052464509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2136 = (1267:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2137) ≤ val WuPaper.ClassicalFourthData.Bq 2137
    have hp : val WuPaper.ClassicalFourthData.Bq 2137 = (168902697952874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2137 = 168902697952874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2137 = (10137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2138) ≤ val WuPaper.ClassicalFourthData.Bq 2138
    have hp : val WuPaper.ClassicalFourthData.Bq 2138 = (168950323565853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2138 = 168950323565853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2138 = (5069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2139) ≤ val WuPaper.ClassicalFourthData.Bq 2139
    have hp : val WuPaper.ClassicalFourthData.Bq 2139 = (168997929312741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2139 = 168997929312741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2139 = (10139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2140) ≤ val WuPaper.ClassicalFourthData.Bq 2140
    have hp : val WuPaper.ClassicalFourthData.Bq 2140 = (169045515202825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2140 = 169045515202825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2140 = (507:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2141) ≤ val WuPaper.ClassicalFourthData.Bq 2141
    have hp : val WuPaper.ClassicalFourthData.Bq 2141 = (169093081245389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2141 = 169093081245389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2141 = (10141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2142) ≤ val WuPaper.ClassicalFourthData.Bq 2142
    have hp : val WuPaper.ClassicalFourthData.Bq 2142 = (169140627449711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2142 = 169140627449711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2142 = (5071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2143) ≤ val WuPaper.ClassicalFourthData.Bq 2143
    have hp : val WuPaper.ClassicalFourthData.Bq 2143 = (169188153825062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2143 = 169188153825062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2143 = (10143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_133
