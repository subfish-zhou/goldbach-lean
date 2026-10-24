import WR2ClassicalCPayments
import WR2ClassicalCPoints035
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_035 (j : Fin 16) : cPayment (16*35+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*35+j.val)+point (1327/200) 4096 (16*35+j.val+1))/2) := by
  fin_cases j
  · change cPayment 560 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 560+point (1327/200) 4096 561)/2)
    have hp : cPayment 560 = (67421225935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 560+point (1327/200) 4096 561)/2 = (3867567:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_560
  · change cPayment 561 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 561+point (1327/200) 4096 562)/2)
    have hp : cPayment 561 = (67481337668:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 561+point (1327/200) 4096 562)/2 = (3868621:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_561
  · change cPayment 562 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 562+point (1327/200) 4096 563)/2)
    have hp : cPayment 562 = (67541295984:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 562+point (1327/200) 4096 563)/2 = (154787:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_562
  · change cPayment 563 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 563+point (1327/200) 4096 564)/2)
    have hp : cPayment 563 = (67601101129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 563+point (1327/200) 4096 564)/2 = (3870729:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_563
  · change cPayment 564 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 564+point (1327/200) 4096 565)/2)
    have hp : cPayment 564 = (67660753346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 564+point (1327/200) 4096 565)/2 = (3871783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_564
  · change cPayment 565 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 565+point (1327/200) 4096 566)/2)
    have hp : cPayment 565 = (67720252882:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 565+point (1327/200) 4096 566)/2 = (3872837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_565
  · change cPayment 566 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 566+point (1327/200) 4096 567)/2)
    have hp : cPayment 566 = (67779599982:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 566+point (1327/200) 4096 567)/2 = (3873891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_566
  · change cPayment 567 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 567+point (1327/200) 4096 568)/2)
    have hp : cPayment 567 = (67838794888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 567+point (1327/200) 4096 568)/2 = (774989:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_567
  · change cPayment 568 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 568+point (1327/200) 4096 569)/2)
    have hp : cPayment 568 = (67897837846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 568+point (1327/200) 4096 569)/2 = (3875999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_568
  · change cPayment 569 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 569+point (1327/200) 4096 570)/2)
    have hp : cPayment 569 = (67956729097:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 569+point (1327/200) 4096 570)/2 = (3877053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_569
  · change cPayment 570 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 570+point (1327/200) 4096 571)/2)
    have hp : cPayment 570 = (68015468886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 570+point (1327/200) 4096 571)/2 = (3878107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_570
  · change cPayment 571 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 571+point (1327/200) 4096 572)/2)
    have hp : cPayment 571 = (68074057454:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 571+point (1327/200) 4096 572)/2 = (3879161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_571
  · change cPayment 572 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 572+point (1327/200) 4096 573)/2)
    have hp : cPayment 572 = (68132495044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 572+point (1327/200) 4096 573)/2 = (776043:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_572
  · change cPayment 573 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 573+point (1327/200) 4096 574)/2)
    have hp : cPayment 573 = (68190781896:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 573+point (1327/200) 4096 574)/2 = (3881269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_573
  · change cPayment 574 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 574+point (1327/200) 4096 575)/2)
    have hp : cPayment 574 = (68248918253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 574+point (1327/200) 4096 575)/2 = (3882323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_574
  · change cPayment 575 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 575+point (1327/200) 4096 576)/2)
    have hp : cPayment 575 = (68306904355:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 575+point (1327/200) 4096 576)/2 = (3883377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_575
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_035
