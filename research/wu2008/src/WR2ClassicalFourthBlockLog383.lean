import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints383
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_383 (j : Fin 16) (hj : 16*383+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*383+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*383+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6128) ≤ val WuPaper.ClassicalFourthData.Bq 6128
    have hp : val WuPaper.ClassicalFourthData.Bq 6128 = (263026473466012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6128 = 263026473466012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6128 = (883:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6129) ≤ val WuPaper.ClassicalFourthData.Bq 6129
    have hp : val WuPaper.ClassicalFourthData.Bq 6129 = (263035808786126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6129 = 263035808786126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6129 = (14129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6130) ≤ val WuPaper.ClassicalFourthData.Bq 6130
    have hp : val WuPaper.ClassicalFourthData.Bq 6130 = (263045140025684:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6130 = 263045140025684 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6130 = (1413:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6131) ≤ val WuPaper.ClassicalFourthData.Bq 6131
    have hp : val WuPaper.ClassicalFourthData.Bq 6131 = (263054467186095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6131 = 263054467186095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6131 = (14131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6132) ≤ val WuPaper.ClassicalFourthData.Bq 6132
    have hp : val WuPaper.ClassicalFourthData.Bq 6132 = (263063790268770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6132 = 263063790268770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6132 = (3533:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6133) ≤ val WuPaper.ClassicalFourthData.Bq 6133
    have hp : val WuPaper.ClassicalFourthData.Bq 6133 = (263073109275119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6133 = 263073109275119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6133 = (14133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6134) ≤ val WuPaper.ClassicalFourthData.Bq 6134
    have hp : val WuPaper.ClassicalFourthData.Bq 6134 = (263082424206553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6134 = 263082424206553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6134 = (7067:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6135) ≤ val WuPaper.ClassicalFourthData.Bq 6135
    have hp : val WuPaper.ClassicalFourthData.Bq 6135 = (263091735064478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6135 = 263091735064478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6135 = (2827:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6135
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6136) ≤ val WuPaper.ClassicalFourthData.Bq 6136
    have hp : val WuPaper.ClassicalFourthData.Bq 6136 = (263101041850304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6136 = 263101041850304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6136 = (1767:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6136
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6137) ≤ val WuPaper.ClassicalFourthData.Bq 6137
    have hp : val WuPaper.ClassicalFourthData.Bq 6137 = (263110344565438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6137 = 263110344565438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6137 = (14137:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6137
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6138) ≤ val WuPaper.ClassicalFourthData.Bq 6138
    have hp : val WuPaper.ClassicalFourthData.Bq 6138 = (263119643211287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6138 = 263119643211287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6138 = (7069:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6138
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6139) ≤ val WuPaper.ClassicalFourthData.Bq 6139
    have hp : val WuPaper.ClassicalFourthData.Bq 6139 = (263128937789258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6139 = 263128937789258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6139 = (14139:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6139
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6140) ≤ val WuPaper.ClassicalFourthData.Bq 6140
    have hp : val WuPaper.ClassicalFourthData.Bq 6140 = (263138228300756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6140 = 263138228300756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6140 = (707:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6140
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6141) ≤ val WuPaper.ClassicalFourthData.Bq 6141
    have hp : val WuPaper.ClassicalFourthData.Bq 6141 = (263147514747188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6141 = 263147514747188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6141 = (14141:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6141
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6142) ≤ val WuPaper.ClassicalFourthData.Bq 6142
    have hp : val WuPaper.ClassicalFourthData.Bq 6142 = (263156797129957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6142 = 263156797129957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6142 = (7071:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6142
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6143) ≤ val WuPaper.ClassicalFourthData.Bq 6143
    have hp : val WuPaper.ClassicalFourthData.Bq 6143 = (263166075450469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6143 = 263166075450469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6143 = (14143:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6143
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_383
