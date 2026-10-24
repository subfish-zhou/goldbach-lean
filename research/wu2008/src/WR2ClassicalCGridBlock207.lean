import WR2ClassicalCPayments
import WR2ClassicalCPoints207
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_207 (j : Fin 16) : cPayment (16*207+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*207+j.val)+point (1327/200) 4096 (16*207+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3312 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3312+point (1327/200) 4096 3313)/2)
    have hp : cPayment 3312 = (25889179458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3312+point (1327/200) 4096 3313)/2 = (270727:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3312
  · change cPayment 3313 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3313+point (1327/200) 4096 3314)/2)
    have hp : cPayment 3313 = (25855168543:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3313+point (1327/200) 4096 3314)/2 = (6769229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3313
  · change cPayment 3314 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3314+point (1327/200) 4096 3315)/2)
    have hp : cPayment 3314 = (25821159139:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3314+point (1327/200) 4096 3315)/2 = (6770283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3314
  · change cPayment 3315 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3315+point (1327/200) 4096 3316)/2)
    have hp : cPayment 3315 = (25787151251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3315+point (1327/200) 4096 3316)/2 = (6771337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3315
  · change cPayment 3316 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3316+point (1327/200) 4096 3317)/2)
    have hp : cPayment 3316 = (25753144884:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3316+point (1327/200) 4096 3317)/2 = (6772391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3316
  · change cPayment 3317 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3317+point (1327/200) 4096 3318)/2)
    have hp : cPayment 3317 = (25719140043:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3317+point (1327/200) 4096 3318)/2 = (1354689:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3317
  · change cPayment 3318 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3318+point (1327/200) 4096 3319)/2)
    have hp : cPayment 3318 = (25685136732:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3318+point (1327/200) 4096 3319)/2 = (6774499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3318
  · change cPayment 3319 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3319+point (1327/200) 4096 3320)/2)
    have hp : cPayment 3319 = (25651134957:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3319+point (1327/200) 4096 3320)/2 = (6775553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3319
  · change cPayment 3320 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3320+point (1327/200) 4096 3321)/2)
    have hp : cPayment 3320 = (25617134721:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3320+point (1327/200) 4096 3321)/2 = (6776607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3320
  · change cPayment 3321 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3321+point (1327/200) 4096 3322)/2)
    have hp : cPayment 3321 = (25583136030:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3321+point (1327/200) 4096 3322)/2 = (6777661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3321
  · change cPayment 3322 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3322+point (1327/200) 4096 3323)/2)
    have hp : cPayment 3322 = (25549138889:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3322+point (1327/200) 4096 3323)/2 = (1355743:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3322
  · change cPayment 3323 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3323+point (1327/200) 4096 3324)/2)
    have hp : cPayment 3323 = (25515143301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3323+point (1327/200) 4096 3324)/2 = (6779769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3323
  · change cPayment 3324 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3324+point (1327/200) 4096 3325)/2)
    have hp : cPayment 3324 = (25481149273:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3324+point (1327/200) 4096 3325)/2 = (6780823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3324
  · change cPayment 3325 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3325+point (1327/200) 4096 3326)/2)
    have hp : cPayment 3325 = (25447156808:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3325+point (1327/200) 4096 3326)/2 = (6781877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3325
  · change cPayment 3326 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3326+point (1327/200) 4096 3327)/2)
    have hp : cPayment 3326 = (25413165911:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3326+point (1327/200) 4096 3327)/2 = (6782931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3326
  · change cPayment 3327 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3327+point (1327/200) 4096 3328)/2)
    have hp : cPayment 3327 = (25379176588:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3327+point (1327/200) 4096 3328)/2 = (1356797:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3327
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_207
