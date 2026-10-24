import WR2ClassicalCPayments
import WR2ClassicalCPoints211
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_211 (j : Fin 16) : cPayment (16*211+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*211+j.val)+point (1327/200) 4096 (16*211+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3376 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3376+point (1327/200) 4096 3377)/2)
    have hp : cPayment 3376 = (23715722794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3376+point (1327/200) 4096 3377)/2 = (6835631:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3376
  · change cPayment 3377 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3377+point (1327/200) 4096 3378)/2)
    have hp : cPayment 3377 = (23681817971:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3377+point (1327/200) 4096 3378)/2 = (1367337:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3377
  · change cPayment 3378 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3378+point (1327/200) 4096 3379)/2)
    have hp : cPayment 3378 = (23647914953:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3378+point (1327/200) 4096 3379)/2 = (6837739:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3378
  · change cPayment 3379 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3379+point (1327/200) 4096 3380)/2)
    have hp : cPayment 3379 = (23614013742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3379+point (1327/200) 4096 3380)/2 = (6838793:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3379
  · change cPayment 3380 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3380+point (1327/200) 4096 3381)/2)
    have hp : cPayment 3380 = (23580114345:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3380+point (1327/200) 4096 3381)/2 = (6839847:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3380
  · change cPayment 3381 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3381+point (1327/200) 4096 3382)/2)
    have hp : cPayment 3381 = (23546216765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3381+point (1327/200) 4096 3382)/2 = (6840901:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3381
  · change cPayment 3382 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3382+point (1327/200) 4096 3383)/2)
    have hp : cPayment 3382 = (23512321007:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3382+point (1327/200) 4096 3383)/2 = (1368391:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3382
  · change cPayment 3383 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3383+point (1327/200) 4096 3384)/2)
    have hp : cPayment 3383 = (23478427075:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3383+point (1327/200) 4096 3384)/2 = (6843009:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3383
  · change cPayment 3384 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3384+point (1327/200) 4096 3385)/2)
    have hp : cPayment 3384 = (23444534973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3384+point (1327/200) 4096 3385)/2 = (6844063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3384
  · change cPayment 3385 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3385+point (1327/200) 4096 3386)/2)
    have hp : cPayment 3385 = (23410644706:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3385+point (1327/200) 4096 3386)/2 = (6845117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3385
  · change cPayment 3386 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3386+point (1327/200) 4096 3387)/2)
    have hp : cPayment 3386 = (23376756278:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3386+point (1327/200) 4096 3387)/2 = (6846171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3386
  · change cPayment 3387 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3387+point (1327/200) 4096 3388)/2)
    have hp : cPayment 3387 = (23342869693:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3387+point (1327/200) 4096 3388)/2 = (273889:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3387
  · change cPayment 3388 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3388+point (1327/200) 4096 3389)/2)
    have hp : cPayment 3388 = (23308984956:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3388+point (1327/200) 4096 3389)/2 = (6848279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3388
  · change cPayment 3389 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3389+point (1327/200) 4096 3390)/2)
    have hp : cPayment 3389 = (23275102071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3389+point (1327/200) 4096 3390)/2 = (6849333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3389
  · change cPayment 3390 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3390+point (1327/200) 4096 3391)/2)
    have hp : cPayment 3390 = (23241221042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3390+point (1327/200) 4096 3391)/2 = (6850387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3390
  · change cPayment 3391 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3391+point (1327/200) 4096 3392)/2)
    have hp : cPayment 3391 = (23207341874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3391+point (1327/200) 4096 3392)/2 = (6851441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3391
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_211
