import WR2ClassicalCPayments
import WR2ClassicalCPoints027
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_027 (j : Fin 16) : cPayment (16*27+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*27+j.val)+point (1327/200) 4096 (16*27+j.val+1))/2) := by
  fin_cases j
  · change cPayment 432 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 432+point (1327/200) 4096 433)/2)
    have hp : cPayment 432 = (58366999035:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 432+point (1327/200) 4096 433)/2 = (746531:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_432
  · change cPayment 433 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 433+point (1327/200) 4096 434)/2)
    have hp : cPayment 433 = (58448943666:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 433+point (1327/200) 4096 434)/2 = (3733709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_433
  · change cPayment 434 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 434+point (1327/200) 4096 435)/2)
    have hp : cPayment 434 = (58530699498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 434+point (1327/200) 4096 435)/2 = (3734763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_434
  · change cPayment 435 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 435+point (1327/200) 4096 436)/2)
    have hp : cPayment 435 = (58612266842:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 435+point (1327/200) 4096 436)/2 = (3735817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_435
  · change cPayment 436 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 436+point (1327/200) 4096 437)/2)
    have hp : cPayment 436 = (58693646005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 436+point (1327/200) 4096 437)/2 = (3736871:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_436
  · change cPayment 437 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 437+point (1327/200) 4096 438)/2)
    have hp : cPayment 437 = (58774837297:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 437+point (1327/200) 4096 438)/2 = (149517:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_437
  · change cPayment 438 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 438+point (1327/200) 4096 439)/2)
    have hp : cPayment 438 = (58855841024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 438+point (1327/200) 4096 439)/2 = (3738979:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_438
  · change cPayment 439 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 439+point (1327/200) 4096 440)/2)
    have hp : cPayment 439 = (58936657494:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 439+point (1327/200) 4096 440)/2 = (3740033:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_439
  · change cPayment 440 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 440+point (1327/200) 4096 441)/2)
    have hp : cPayment 440 = (59017287014:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 440+point (1327/200) 4096 441)/2 = (3741087:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_440
  · change cPayment 441 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 441+point (1327/200) 4096 442)/2)
    have hp : cPayment 441 = (59097729888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 441+point (1327/200) 4096 442)/2 = (3742141:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_441
  · change cPayment 442 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 442+point (1327/200) 4096 443)/2)
    have hp : cPayment 442 = (59177986423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 442+point (1327/200) 4096 443)/2 = (748639:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_442
  · change cPayment 443 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 443+point (1327/200) 4096 444)/2)
    have hp : cPayment 443 = (59258056924:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 443+point (1327/200) 4096 444)/2 = (3744249:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_443
  · change cPayment 444 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 444+point (1327/200) 4096 445)/2)
    have hp : cPayment 444 = (59337941694:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 444+point (1327/200) 4096 445)/2 = (3745303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_444
  · change cPayment 445 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 445+point (1327/200) 4096 446)/2)
    have hp : cPayment 445 = (59417641037:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 445+point (1327/200) 4096 446)/2 = (3746357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_445
  · change cPayment 446 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 446+point (1327/200) 4096 447)/2)
    have hp : cPayment 446 = (59497155257:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 446+point (1327/200) 4096 447)/2 = (3747411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_446
  · change cPayment 447 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 447+point (1327/200) 4096 448)/2)
    have hp : cPayment 447 = (59576484656:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 447+point (1327/200) 4096 448)/2 = (749693:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_447
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_027
