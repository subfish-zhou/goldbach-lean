import WR2ClassicalCPayments
import WR2ClassicalCPoints032
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_032 (j : Fin 16) : cPayment (16*32+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*32+j.val)+point (1327/200) 4096 (16*32+j.val+1))/2) := by
  fin_cases j
  · change cPayment 512 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 512+point (1327/200) 4096 513)/2)
    have hp : cPayment 512 = (64350514471:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 512+point (1327/200) 4096 513)/2 = (152679:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_512
  · change cPayment 513 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 513+point (1327/200) 4096 514)/2)
    have hp : cPayment 513 = (64418288073:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 513+point (1327/200) 4096 514)/2 = (3818029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_513
  · change cPayment 514 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 514+point (1327/200) 4096 515)/2)
    have hp : cPayment 514 = (64485895929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 514+point (1327/200) 4096 515)/2 = (3819083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_514
  · change cPayment 515 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 515+point (1327/200) 4096 516)/2)
    have hp : cPayment 515 = (64553338309:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 515+point (1327/200) 4096 516)/2 = (3820137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_515
  · change cPayment 516 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 516+point (1327/200) 4096 517)/2)
    have hp : cPayment 516 = (64620615479:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 516+point (1327/200) 4096 517)/2 = (3821191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_516
  · change cPayment 517 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 517+point (1327/200) 4096 518)/2)
    have hp : cPayment 517 = (64687727706:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 517+point (1327/200) 4096 518)/2 = (764449:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_517
  · change cPayment 518 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 518+point (1327/200) 4096 519)/2)
    have hp : cPayment 518 = (64754675257:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 518+point (1327/200) 4096 519)/2 = (3823299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_518
  · change cPayment 519 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 519+point (1327/200) 4096 520)/2)
    have hp : cPayment 519 = (64821458396:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 519+point (1327/200) 4096 520)/2 = (3824353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_519
  · change cPayment 520 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 520+point (1327/200) 4096 521)/2)
    have hp : cPayment 520 = (64888077389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 520+point (1327/200) 4096 521)/2 = (3825407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_520
  · change cPayment 521 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 521+point (1327/200) 4096 522)/2)
    have hp : cPayment 521 = (64954532502:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 521+point (1327/200) 4096 522)/2 = (3826461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_521
  · change cPayment 522 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 522+point (1327/200) 4096 523)/2)
    have hp : cPayment 522 = (65020823998:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 522+point (1327/200) 4096 523)/2 = (765503:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_522
  · change cPayment 523 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 523+point (1327/200) 4096 524)/2)
    have hp : cPayment 523 = (65086952141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 523+point (1327/200) 4096 524)/2 = (3828569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_523
  · change cPayment 524 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 524+point (1327/200) 4096 525)/2)
    have hp : cPayment 524 = (65152917195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 524+point (1327/200) 4096 525)/2 = (3829623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_524
  · change cPayment 525 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 525+point (1327/200) 4096 526)/2)
    have hp : cPayment 525 = (65218719423:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 525+point (1327/200) 4096 526)/2 = (3830677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_525
  · change cPayment 526 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 526+point (1327/200) 4096 527)/2)
    have hp : cPayment 526 = (65284359087:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 526+point (1327/200) 4096 527)/2 = (3831731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_526
  · change cPayment 527 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 527+point (1327/200) 4096 528)/2)
    have hp : cPayment 527 = (65349836449:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 527+point (1327/200) 4096 528)/2 = (766557:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_527
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_032
