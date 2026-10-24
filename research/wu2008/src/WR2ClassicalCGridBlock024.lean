import WR2ClassicalCPayments
import WR2ClassicalCPoints024
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_024 (j : Fin 16) : cPayment (16*24+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*24+j.val)+point (1327/200) 4096 (16*24+j.val+1))/2) := by
  fin_cases j
  · change cPayment 384 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 384+point (1327/200) 4096 385)/2)
    have hp : cPayment 384 = (54205423096:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 384+point (1327/200) 4096 385)/2 = (3682063:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_384
  · change cPayment 385 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 385+point (1327/200) 4096 386)/2)
    have hp : cPayment 385 = (54296805182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 385+point (1327/200) 4096 386)/2 = (3683117:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_385
  · change cPayment 386 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 386+point (1327/200) 4096 387)/2)
    have hp : cPayment 386 = (54387982933:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 386+point (1327/200) 4096 387)/2 = (3684171:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_386
  · change cPayment 387 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 387+point (1327/200) 4096 388)/2)
    have hp : cPayment 387 = (54478956688:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 387+point (1327/200) 4096 388)/2 = (147409:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_387
  · change cPayment 388 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 388+point (1327/200) 4096 389)/2)
    have hp : cPayment 388 = (54569726783:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 388+point (1327/200) 4096 389)/2 = (3686279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_388
  · change cPayment 389 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 389+point (1327/200) 4096 390)/2)
    have hp : cPayment 389 = (54660293556:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 389+point (1327/200) 4096 390)/2 = (3687333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_389
  · change cPayment 390 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 390+point (1327/200) 4096 391)/2)
    have hp : cPayment 390 = (54750657342:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 390+point (1327/200) 4096 391)/2 = (3688387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_390
  · change cPayment 391 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 391+point (1327/200) 4096 392)/2)
    have hp : cPayment 391 = (54840818477:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 391+point (1327/200) 4096 392)/2 = (3689441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_391
  · change cPayment 392 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 392+point (1327/200) 4096 393)/2)
    have hp : cPayment 392 = (54930777296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 392+point (1327/200) 4096 393)/2 = (738099:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_392
  · change cPayment 393 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 393+point (1327/200) 4096 394)/2)
    have hp : cPayment 393 = (55020534132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 393+point (1327/200) 4096 394)/2 = (3691549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_393
  · change cPayment 394 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 394+point (1327/200) 4096 395)/2)
    have hp : cPayment 394 = (55110089320:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 394+point (1327/200) 4096 395)/2 = (3692603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_394
  · change cPayment 395 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 395+point (1327/200) 4096 396)/2)
    have hp : cPayment 395 = (55199443193:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 395+point (1327/200) 4096 396)/2 = (3693657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_395
  · change cPayment 396 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 396+point (1327/200) 4096 397)/2)
    have hp : cPayment 396 = (55288596082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 396+point (1327/200) 4096 397)/2 = (3694711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_396
  · change cPayment 397 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 397+point (1327/200) 4096 398)/2)
    have hp : cPayment 397 = (55377548319:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 397+point (1327/200) 4096 398)/2 = (739153:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_397
  · change cPayment 398 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 398+point (1327/200) 4096 399)/2)
    have hp : cPayment 398 = (55466300237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 398+point (1327/200) 4096 399)/2 = (3696819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_398
  · change cPayment 399 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 399+point (1327/200) 4096 400)/2)
    have hp : cPayment 399 = (55554852164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 399+point (1327/200) 4096 400)/2 = (3697873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_399
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_024
