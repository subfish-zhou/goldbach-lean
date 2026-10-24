import WR2ClassicalCPayments
import WR2ClassicalCPoints220
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_220 (j : Fin 16) : cPayment (16*220+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*220+j.val)+point (1327/200) 4096 (16*220+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3520 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3520+point (1327/200) 4096 3521)/2)
    have hp : cPayment 3520 = (18854032300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3520+point (1327/200) 4096 3521)/2 = (6987407:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3520
  · change cPayment 3521 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3521+point (1327/200) 4096 3522)/2)
    have hp : cPayment 3521 = (18820429410:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3521+point (1327/200) 4096 3522)/2 = (6988461:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3521
  · change cPayment 3522 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3522+point (1327/200) 4096 3523)/2)
    have hp : cPayment 3522 = (18786828894:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3522+point (1327/200) 4096 3523)/2 = (1397903:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3522
  · change cPayment 3523 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3523+point (1327/200) 4096 3524)/2)
    have hp : cPayment 3523 = (18753230756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3523+point (1327/200) 4096 3524)/2 = (6990569:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3523
  · change cPayment 3524 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3524+point (1327/200) 4096 3525)/2)
    have hp : cPayment 3524 = (18719634998:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3524+point (1327/200) 4096 3525)/2 = (6991623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3524
  · change cPayment 3525 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3525+point (1327/200) 4096 3526)/2)
    have hp : cPayment 3525 = (18686041625:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3525+point (1327/200) 4096 3526)/2 = (6992677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3525
  · change cPayment 3526 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3526+point (1327/200) 4096 3527)/2)
    have hp : cPayment 3526 = (18652450639:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3526+point (1327/200) 4096 3527)/2 = (6993731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3526
  · change cPayment 3527 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3527+point (1327/200) 4096 3528)/2)
    have hp : cPayment 3527 = (18618862045:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3527+point (1327/200) 4096 3528)/2 = (1398957:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3527
  · change cPayment 3528 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3528+point (1327/200) 4096 3529)/2)
    have hp : cPayment 3528 = (18585275847:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3528+point (1327/200) 4096 3529)/2 = (6995839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3528
  · change cPayment 3529 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3529+point (1327/200) 4096 3530)/2)
    have hp : cPayment 3529 = (18551692046:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3529+point (1327/200) 4096 3530)/2 = (6996893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3529
  · change cPayment 3530 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3530+point (1327/200) 4096 3531)/2)
    have hp : cPayment 3530 = (18518110648:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3530+point (1327/200) 4096 3531)/2 = (6997947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3530
  · change cPayment 3531 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3531+point (1327/200) 4096 3532)/2)
    have hp : cPayment 3531 = (18484531655:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3531+point (1327/200) 4096 3532)/2 = (6999001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3531
  · change cPayment 3532 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3532+point (1327/200) 4096 3533)/2)
    have hp : cPayment 3532 = (18450955072:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3532+point (1327/200) 4096 3533)/2 = (1400011:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3532
  · change cPayment 3533 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3533+point (1327/200) 4096 3534)/2)
    have hp : cPayment 3533 = (18417380901:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3533+point (1327/200) 4096 3534)/2 = (7001109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3533
  · change cPayment 3534 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3534+point (1327/200) 4096 3535)/2)
    have hp : cPayment 3534 = (18383809146:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3534+point (1327/200) 4096 3535)/2 = (7002163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3534
  · change cPayment 3535 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3535+point (1327/200) 4096 3536)/2)
    have hp : cPayment 3535 = (18350239811:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3535+point (1327/200) 4096 3536)/2 = (7003217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3535
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_220
