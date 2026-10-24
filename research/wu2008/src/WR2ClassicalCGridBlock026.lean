import WR2ClassicalCPayments
import WR2ClassicalCPoints026
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_026 (j : Fin 16) : cPayment (16*26+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*26+j.val)+point (1327/200) 4096 (16*26+j.val+1))/2) := by
  fin_cases j
  · change cPayment 416 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 416+point (1327/200) 4096 417)/2)
    have hp : cPayment 416 = (57029953785:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 416+point (1327/200) 4096 417)/2 = (3715791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_416
  · change cPayment 417 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 417+point (1327/200) 4096 418)/2)
    have hp : cPayment 417 = (57114961719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 417+point (1327/200) 4096 418)/2 = (743369:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_417
  · change cPayment 418 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 418+point (1327/200) 4096 419)/2)
    have hp : cPayment 418 = (57199775827:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 418+point (1327/200) 4096 419)/2 = (3717899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_418
  · change cPayment 419 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 419+point (1327/200) 4096 420)/2)
    have hp : cPayment 419 = (57284396430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 419+point (1327/200) 4096 420)/2 = (3718953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_419
  · change cPayment 420 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 420+point (1327/200) 4096 421)/2)
    have hp : cPayment 420 = (57368823843:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 420+point (1327/200) 4096 421)/2 = (3720007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_420
  · change cPayment 421 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 421+point (1327/200) 4096 422)/2)
    have hp : cPayment 421 = (57453058386:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 421+point (1327/200) 4096 422)/2 = (3721061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_421
  · change cPayment 422 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 422+point (1327/200) 4096 423)/2)
    have hp : cPayment 422 = (57537100374:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 422+point (1327/200) 4096 423)/2 = (744423:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_422
  · change cPayment 423 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 423+point (1327/200) 4096 424)/2)
    have hp : cPayment 423 = (57620950124:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 423+point (1327/200) 4096 424)/2 = (3723169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_423
  · change cPayment 424 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 424+point (1327/200) 4096 425)/2)
    have hp : cPayment 424 = (57704607951:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 424+point (1327/200) 4096 425)/2 = (3724223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_424
  · change cPayment 425 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 425+point (1327/200) 4096 426)/2)
    have hp : cPayment 425 = (57788074170:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 425+point (1327/200) 4096 426)/2 = (3725277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_425
  · change cPayment 426 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 426+point (1327/200) 4096 427)/2)
    have hp : cPayment 426 = (57871349097:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 426+point (1327/200) 4096 427)/2 = (3726331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_426
  · change cPayment 427 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 427+point (1327/200) 4096 428)/2)
    have hp : cPayment 427 = (57954433044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 427+point (1327/200) 4096 428)/2 = (745477:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_427
  · change cPayment 428 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 428+point (1327/200) 4096 429)/2)
    have hp : cPayment 428 = (58037326325:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 428+point (1327/200) 4096 429)/2 = (3728439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_428
  · change cPayment 429 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 429+point (1327/200) 4096 430)/2)
    have hp : cPayment 429 = (58120029253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 429+point (1327/200) 4096 430)/2 = (3729493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_429
  · change cPayment 430 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 430+point (1327/200) 4096 431)/2)
    have hp : cPayment 430 = (58202542139:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 430+point (1327/200) 4096 431)/2 = (3730547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_430
  · change cPayment 431 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 431+point (1327/200) 4096 432)/2)
    have hp : cPayment 431 = (58284865296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 431+point (1327/200) 4096 432)/2 = (3731601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_431
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_026
