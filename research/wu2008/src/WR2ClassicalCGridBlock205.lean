import WR2ClassicalCPayments
import WR2ClassicalCPoints205
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_205 (j : Fin 16) : cPayment (16*205+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*205+j.val)+point (1327/200) 4096 (16*205+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3280 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3280+point (1327/200) 4096 3281)/2)
    have hp : cPayment 3280 = (26978297800:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3280+point (1327/200) 4096 3281)/2 = (6734447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3280
  · change cPayment 3281 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3281+point (1327/200) 4096 3282)/2)
    have hp : cPayment 3281 = (26944241084:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3281+point (1327/200) 4096 3282)/2 = (6735501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3281
  · change cPayment 3282 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3282+point (1327/200) 4096 3283)/2)
    have hp : cPayment 3282 = (26910185724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3282+point (1327/200) 4096 3283)/2 = (1347311:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3282
  · change cPayment 3283 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3283+point (1327/200) 4096 3284)/2)
    have hp : cPayment 3283 = (26876131724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3283+point (1327/200) 4096 3284)/2 = (6737609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3283
  · change cPayment 3284 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3284+point (1327/200) 4096 3285)/2)
    have hp : cPayment 3284 = (26842079088:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3284+point (1327/200) 4096 3285)/2 = (6738663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3284
  · change cPayment 3285 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3285+point (1327/200) 4096 3286)/2)
    have hp : cPayment 3285 = (26808027822:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3285+point (1327/200) 4096 3286)/2 = (6739717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3285
  · change cPayment 3286 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3286+point (1327/200) 4096 3287)/2)
    have hp : cPayment 3286 = (26773977931:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3286+point (1327/200) 4096 3287)/2 = (6740771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3286
  · change cPayment 3287 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3287+point (1327/200) 4096 3288)/2)
    have hp : cPayment 3287 = (26739929420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3287+point (1327/200) 4096 3288)/2 = (269673:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3287
  · change cPayment 3288 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3288+point (1327/200) 4096 3289)/2)
    have hp : cPayment 3288 = (26705882293:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3288+point (1327/200) 4096 3289)/2 = (6742879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3288
  · change cPayment 3289 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3289+point (1327/200) 4096 3290)/2)
    have hp : cPayment 3289 = (26671836557:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3289+point (1327/200) 4096 3290)/2 = (6743933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3289
  · change cPayment 3290 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3290+point (1327/200) 4096 3291)/2)
    have hp : cPayment 3290 = (26637792214:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3290+point (1327/200) 4096 3291)/2 = (6744987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3290
  · change cPayment 3291 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3291+point (1327/200) 4096 3292)/2)
    have hp : cPayment 3291 = (26603749272:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3291+point (1327/200) 4096 3292)/2 = (6746041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3291
  · change cPayment 3292 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3292+point (1327/200) 4096 3293)/2)
    have hp : cPayment 3292 = (26569707734:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3292+point (1327/200) 4096 3293)/2 = (1349419:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3292
  · change cPayment 3293 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3293+point (1327/200) 4096 3294)/2)
    have hp : cPayment 3293 = (26535667605:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3293+point (1327/200) 4096 3294)/2 = (6748149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3293
  · change cPayment 3294 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3294+point (1327/200) 4096 3295)/2)
    have hp : cPayment 3294 = (26501628891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3294+point (1327/200) 4096 3295)/2 = (6749203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3294
  · change cPayment 3295 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3295+point (1327/200) 4096 3296)/2)
    have hp : cPayment 3295 = (26467591596:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3295+point (1327/200) 4096 3296)/2 = (6750257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3295
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_205
