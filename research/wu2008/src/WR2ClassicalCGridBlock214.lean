import WR2ClassicalCPayments
import WR2ClassicalCPoints214
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_214 (j : Fin 16) : cPayment (16*214+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*214+j.val)+point (1327/200) 4096 (16*214+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3424 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3424+point (1327/200) 4096 3425)/2)
    have hp : cPayment 3424 = (22090400861:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3424+point (1327/200) 4096 3425)/2 = (6886223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3424
  · change cPayment 3425 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3425+point (1327/200) 4096 3426)/2)
    have hp : cPayment 3425 = (22056587465:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3425+point (1327/200) 4096 3426)/2 = (6887277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3425
  · change cPayment 3426 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3426+point (1327/200) 4096 3427)/2)
    have hp : cPayment 3426 = (22022776077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3426+point (1327/200) 4096 3427)/2 = (6888331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3426
  · change cPayment 3427 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3427+point (1327/200) 4096 3428)/2)
    have hp : cPayment 3427 = (21988966700:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3427+point (1327/200) 4096 3428)/2 = (1377877:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3427
  · change cPayment 3428 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3428+point (1327/200) 4096 3429)/2)
    have hp : cPayment 3428 = (21955159338:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3428+point (1327/200) 4096 3429)/2 = (6890439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3428
  · change cPayment 3429 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3429+point (1327/200) 4096 3430)/2)
    have hp : cPayment 3429 = (21921353996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3429+point (1327/200) 4096 3430)/2 = (6891493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3429
  · change cPayment 3430 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3430+point (1327/200) 4096 3431)/2)
    have hp : cPayment 3430 = (21887550677:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3430+point (1327/200) 4096 3431)/2 = (6892547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3430
  · change cPayment 3431 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3431+point (1327/200) 4096 3432)/2)
    have hp : cPayment 3431 = (21853749386:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3431+point (1327/200) 4096 3432)/2 = (6893601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3431
  · change cPayment 3432 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3432+point (1327/200) 4096 3433)/2)
    have hp : cPayment 3432 = (21819950127:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3432+point (1327/200) 4096 3433)/2 = (1378931:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3432
  · change cPayment 3433 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3433+point (1327/200) 4096 3434)/2)
    have hp : cPayment 3433 = (21786152903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3433+point (1327/200) 4096 3434)/2 = (6895709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3433
  · change cPayment 3434 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3434+point (1327/200) 4096 3435)/2)
    have hp : cPayment 3434 = (21752357718:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3434+point (1327/200) 4096 3435)/2 = (6896763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3434
  · change cPayment 3435 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3435+point (1327/200) 4096 3436)/2)
    have hp : cPayment 3435 = (21718564578:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3435+point (1327/200) 4096 3436)/2 = (6897817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3435
  · change cPayment 3436 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3436+point (1327/200) 4096 3437)/2)
    have hp : cPayment 3436 = (21684773485:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3436+point (1327/200) 4096 3437)/2 = (6898871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3436
  · change cPayment 3437 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3437+point (1327/200) 4096 3438)/2)
    have hp : cPayment 3437 = (21650984444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3437+point (1327/200) 4096 3438)/2 = (275997:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3437
  · change cPayment 3438 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3438+point (1327/200) 4096 3439)/2)
    have hp : cPayment 3438 = (21617197459:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3438+point (1327/200) 4096 3439)/2 = (6900979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3438
  · change cPayment 3439 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3439+point (1327/200) 4096 3440)/2)
    have hp : cPayment 3439 = (21583412534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3439+point (1327/200) 4096 3440)/2 = (6902033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3439
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_214
