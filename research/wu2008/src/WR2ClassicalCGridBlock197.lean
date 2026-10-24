import WR2ClassicalCPayments
import WR2ClassicalCPoints197
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_197 (j : Fin 16) : cPayment (16*197+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*197+j.val)+point (1327/200) 4096 (16*197+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3152 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3152+point (1327/200) 4096 3153)/2)
    have hp : cPayment 3152 = (31346871204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3152+point (1327/200) 4096 3153)/2 = (1319907:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3152
  · change cPayment 3153 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3153+point (1327/200) 4096 3154)/2)
    have hp : cPayment 3153 = (31312684908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3153+point (1327/200) 4096 3154)/2 = (6600589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3153
  · change cPayment 3154 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3154+point (1327/200) 4096 3155)/2)
    have hp : cPayment 3154 = (31278499267:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3154+point (1327/200) 4096 3155)/2 = (6601643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3154
  · change cPayment 3155 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3155+point (1327/200) 4096 3156)/2)
    have hp : cPayment 3155 = (31244314288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3155+point (1327/200) 4096 3156)/2 = (6602697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3155
  · change cPayment 3156 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3156+point (1327/200) 4096 3157)/2)
    have hp : cPayment 3156 = (31210129974:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3156+point (1327/200) 4096 3157)/2 = (6603751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3156
  · change cPayment 3157 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3157+point (1327/200) 4096 3158)/2)
    have hp : cPayment 3157 = (31175946334:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3157+point (1327/200) 4096 3158)/2 = (1320961:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3157
  · change cPayment 3158 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3158+point (1327/200) 4096 3159)/2)
    have hp : cPayment 3158 = (31141763372:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3158+point (1327/200) 4096 3159)/2 = (6605859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3158
  · change cPayment 3159 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3159+point (1327/200) 4096 3160)/2)
    have hp : cPayment 3159 = (31107581095:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3159+point (1327/200) 4096 3160)/2 = (6606913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3159
  · change cPayment 3160 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3160+point (1327/200) 4096 3161)/2)
    have hp : cPayment 3160 = (31073399508:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3160+point (1327/200) 4096 3161)/2 = (6607967:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3160
  · change cPayment 3161 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3161+point (1327/200) 4096 3162)/2)
    have hp : cPayment 3161 = (31039218617:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3161+point (1327/200) 4096 3162)/2 = (6609021:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3161
  · change cPayment 3162 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3162+point (1327/200) 4096 3163)/2)
    have hp : cPayment 3162 = (31005038429:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3162+point (1327/200) 4096 3163)/2 = (264403:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3162
  · change cPayment 3163 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3163+point (1327/200) 4096 3164)/2)
    have hp : cPayment 3163 = (30970858949:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3163+point (1327/200) 4096 3164)/2 = (6611129:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3163
  · change cPayment 3164 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3164+point (1327/200) 4096 3165)/2)
    have hp : cPayment 3164 = (30936680182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3164+point (1327/200) 4096 3165)/2 = (6612183:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3164
  · change cPayment 3165 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3165+point (1327/200) 4096 3166)/2)
    have hp : cPayment 3165 = (30902502136:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3165+point (1327/200) 4096 3166)/2 = (6613237:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3165
  · change cPayment 3166 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3166+point (1327/200) 4096 3167)/2)
    have hp : cPayment 3166 = (30868324816:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3166+point (1327/200) 4096 3167)/2 = (6614291:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3166
  · change cPayment 3167 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3167+point (1327/200) 4096 3168)/2)
    have hp : cPayment 3167 = (30834148227:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3167+point (1327/200) 4096 3168)/2 = (1323069:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3167
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_197
