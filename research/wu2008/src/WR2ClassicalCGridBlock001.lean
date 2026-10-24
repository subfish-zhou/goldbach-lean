import WR2ClassicalCPayments
import WR2ClassicalCPoints001
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_001 (j : Fin 16) : cPayment (16*1+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*1+j.val)+point (1327/200) 4096 (16*1+j.val+1))/2) := by
  fin_cases j
  · change cPayment 16 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 16+point (1327/200) 4096 17)/2)
    have hp : cPayment 16 = (3291899807:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 16+point (1327/200) 4096 17)/2 = (3294191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_16
  · change cPayment 17 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 17+point (1327/200) 4096 18)/2)
    have hp : cPayment 17 = (3487990520:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 17+point (1327/200) 4096 18)/2 = (659049:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_17
  · change cPayment 18 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 18+point (1327/200) 4096 19)/2)
    have hp : cPayment 18 = (3683694941:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 18+point (1327/200) 4096 19)/2 = (3296299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_18
  · change cPayment 19 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 19+point (1327/200) 4096 20)/2)
    have hp : cPayment 19 = (3879013771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 19+point (1327/200) 4096 20)/2 = (3297353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_19
  · change cPayment 20 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 20+point (1327/200) 4096 21)/2)
    have hp : cPayment 20 = (4073947713:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 20+point (1327/200) 4096 21)/2 = (3298407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_20
  · change cPayment 21 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 21+point (1327/200) 4096 22)/2)
    have hp : cPayment 21 = (4268497464:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 21+point (1327/200) 4096 22)/2 = (3299461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_21
  · change cPayment 22 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 22+point (1327/200) 4096 23)/2)
    have hp : cPayment 22 = (4462663724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 22+point (1327/200) 4096 23)/2 = (660103:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_22
  · change cPayment 23 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 23+point (1327/200) 4096 24)/2)
    have hp : cPayment 23 = (4656447188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 23+point (1327/200) 4096 24)/2 = (3301569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_23
  · change cPayment 24 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 24+point (1327/200) 4096 25)/2)
    have hp : cPayment 24 = (4849848553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 24+point (1327/200) 4096 25)/2 = (3302623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_24
  · change cPayment 25 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 25+point (1327/200) 4096 26)/2)
    have hp : cPayment 25 = (5042868511:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 25+point (1327/200) 4096 26)/2 = (3303677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_25
  · change cPayment 26 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 26+point (1327/200) 4096 27)/2)
    have hp : cPayment 26 = (5235507754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 26+point (1327/200) 4096 27)/2 = (3304731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_26
  · change cPayment 27 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 27+point (1327/200) 4096 28)/2)
    have hp : cPayment 27 = (5427766973:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 27+point (1327/200) 4096 28)/2 = (661157:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_27
  · change cPayment 28 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 28+point (1327/200) 4096 29)/2)
    have hp : cPayment 28 = (5619646858:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 28+point (1327/200) 4096 29)/2 = (3306839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_28
  · change cPayment 29 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 29+point (1327/200) 4096 30)/2)
    have hp : cPayment 29 = (5811148095:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 29+point (1327/200) 4096 30)/2 = (3307893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_29
  · change cPayment 30 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 30+point (1327/200) 4096 31)/2)
    have hp : cPayment 30 = (6002271371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 30+point (1327/200) 4096 31)/2 = (3308947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_30
  · change cPayment 31 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 31+point (1327/200) 4096 32)/2)
    have hp : cPayment 31 = (6193017371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 31+point (1327/200) 4096 32)/2 = (3310001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_31
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_001
