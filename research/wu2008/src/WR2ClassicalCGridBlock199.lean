import WR2ClassicalCPayments
import WR2ClassicalCPoints199
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_199 (j : Fin 16) : cPayment (16*199+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*199+j.val)+point (1327/200) 4096 (16*199+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3184 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3184+point (1327/200) 4096 3185)/2)
    have hp : cPayment 3184 = (30253263799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3184+point (1327/200) 4096 3185)/2 = (6633263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3184
  · change cPayment 3185 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3185+point (1327/200) 4096 3186)/2)
    have hp : cPayment 3185 = (30219101373:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3185+point (1327/200) 4096 3186)/2 = (6634317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3185
  · change cPayment 3186 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3186+point (1327/200) 4096 3187)/2)
    have hp : cPayment 3186 = (30184939789:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3186+point (1327/200) 4096 3187)/2 = (6635371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3186
  · change cPayment 3187 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3187+point (1327/200) 4096 3188)/2)
    have hp : cPayment 3187 = (30150779051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3187+point (1327/200) 4096 3188)/2 = (265457:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3187
  · change cPayment 3188 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3188+point (1327/200) 4096 3189)/2)
    have hp : cPayment 3188 = (30116619167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3188+point (1327/200) 4096 3189)/2 = (6637479:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3188
  · change cPayment 3189 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3189+point (1327/200) 4096 3190)/2)
    have hp : cPayment 3189 = (30082460141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3189+point (1327/200) 4096 3190)/2 = (6638533:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3189
  · change cPayment 3190 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3190+point (1327/200) 4096 3191)/2)
    have hp : cPayment 3190 = (30048301980:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3190+point (1327/200) 4096 3191)/2 = (6639587:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3190
  · change cPayment 3191 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3191+point (1327/200) 4096 3192)/2)
    have hp : cPayment 3191 = (30014144688:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3191+point (1327/200) 4096 3192)/2 = (6640641:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3191
  · change cPayment 3192 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3192+point (1327/200) 4096 3193)/2)
    have hp : cPayment 3192 = (29979988272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3192+point (1327/200) 4096 3193)/2 = (1328339:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3192
  · change cPayment 3193 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3193+point (1327/200) 4096 3194)/2)
    have hp : cPayment 3193 = (29945832737:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3193+point (1327/200) 4096 3194)/2 = (6642749:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3193
  · change cPayment 3194 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3194+point (1327/200) 4096 3195)/2)
    have hp : cPayment 3194 = (29911678090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3194+point (1327/200) 4096 3195)/2 = (6643803:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3194
  · change cPayment 3195 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3195+point (1327/200) 4096 3196)/2)
    have hp : cPayment 3195 = (29877524335:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3195+point (1327/200) 4096 3196)/2 = (6644857:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3195
  · change cPayment 3196 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3196+point (1327/200) 4096 3197)/2)
    have hp : cPayment 3196 = (29843371478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3196+point (1327/200) 4096 3197)/2 = (6645911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3196
  · change cPayment 3197 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3197+point (1327/200) 4096 3198)/2)
    have hp : cPayment 3197 = (29809219524:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3197+point (1327/200) 4096 3198)/2 = (1329393:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3197
  · change cPayment 3198 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3198+point (1327/200) 4096 3199)/2)
    have hp : cPayment 3198 = (29775068481:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3198+point (1327/200) 4096 3199)/2 = (6648019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3198
  · change cPayment 3199 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3199+point (1327/200) 4096 3200)/2)
    have hp : cPayment 3199 = (29740918352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3199+point (1327/200) 4096 3200)/2 = (6649073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3199
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_199
