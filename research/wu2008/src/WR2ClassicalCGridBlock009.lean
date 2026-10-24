import WR2ClassicalCPayments
import WR2ClassicalCPoints009
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_009 (j : Fin 16) : cPayment (16*9+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*9+j.val)+point (1327/200) 4096 (16*9+j.val+1))/2) := by
  fin_cases j
  · change cPayment 144 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 144+point (1327/200) 4096 145)/2)
    have hp : cPayment 144 = (25476493400:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 144+point (1327/200) 4096 145)/2 = (3429103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_144
  · change cPayment 145 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 145+point (1327/200) 4096 146)/2)
    have hp : cPayment 145 = (25628374590:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 145+point (1327/200) 4096 146)/2 = (3430157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_145
  · change cPayment 146 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 146+point (1327/200) 4096 147)/2)
    have hp : cPayment 146 = (25779948413:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 146+point (1327/200) 4096 147)/2 = (3431211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_146
  · change cPayment 147 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 147+point (1327/200) 4096 148)/2)
    have hp : cPayment 147 = (25931215408:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 147+point (1327/200) 4096 148)/2 = (686453:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_147
  · change cPayment 148 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 148+point (1327/200) 4096 149)/2)
    have hp : cPayment 148 = (26082176111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 148+point (1327/200) 4096 149)/2 = (3433319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_148
  · change cPayment 149 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 149+point (1327/200) 4096 150)/2)
    have hp : cPayment 149 = (26232831059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 149+point (1327/200) 4096 150)/2 = (3434373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_149
  · change cPayment 150 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 150+point (1327/200) 4096 151)/2)
    have hp : cPayment 150 = (26383180787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 150+point (1327/200) 4096 151)/2 = (3435427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_150
  · change cPayment 151 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 151+point (1327/200) 4096 152)/2)
    have hp : cPayment 151 = (26533225828:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 151+point (1327/200) 4096 152)/2 = (3436481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_151
  · change cPayment 152 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 152+point (1327/200) 4096 153)/2)
    have hp : cPayment 152 = (26682966716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 152+point (1327/200) 4096 153)/2 = (687507:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_152
  · change cPayment 153 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 153+point (1327/200) 4096 154)/2)
    have hp : cPayment 153 = (26832403981:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 153+point (1327/200) 4096 154)/2 = (3438589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_153
  · change cPayment 154 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 154+point (1327/200) 4096 155)/2)
    have hp : cPayment 154 = (26981538155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 154+point (1327/200) 4096 155)/2 = (3439643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_154
  · change cPayment 155 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 155+point (1327/200) 4096 156)/2)
    have hp : cPayment 155 = (27130369767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 155+point (1327/200) 4096 156)/2 = (3440697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_155
  · change cPayment 156 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 156+point (1327/200) 4096 157)/2)
    have hp : cPayment 156 = (27278899346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 156+point (1327/200) 4096 157)/2 = (3441751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_156
  · change cPayment 157 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 157+point (1327/200) 4096 158)/2)
    have hp : cPayment 157 = (27427127418:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 157+point (1327/200) 4096 158)/2 = (688561:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_157
  · change cPayment 158 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 158+point (1327/200) 4096 159)/2)
    have hp : cPayment 158 = (27575054511:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 158+point (1327/200) 4096 159)/2 = (3443859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_158
  · change cPayment 159 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 159+point (1327/200) 4096 160)/2)
    have hp : cPayment 159 = (27722681150:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 159+point (1327/200) 4096 160)/2 = (3444913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_159
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_009
