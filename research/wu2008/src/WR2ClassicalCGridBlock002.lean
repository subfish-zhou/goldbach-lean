import WR2ClassicalCPayments
import WR2ClassicalCPoints002
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_002 (j : Fin 16) : cPayment (16*2+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*2+j.val)+point (1327/200) 4096 (16*2+j.val+1))/2) := by
  fin_cases j
  · change cPayment 32 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 32+point (1327/200) 4096 33)/2)
    have hp : cPayment 32 = (6383386778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 32+point (1327/200) 4096 33)/2 = (662211:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_32
  · change cPayment 33 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 33+point (1327/200) 4096 34)/2)
    have hp : cPayment 33 = (6573380274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 33+point (1327/200) 4096 34)/2 = (3312109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_33
  · change cPayment 34 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 34+point (1327/200) 4096 35)/2)
    have hp : cPayment 34 = (6762998540:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 34+point (1327/200) 4096 35)/2 = (3313163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_34
  · change cPayment 35 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 35+point (1327/200) 4096 36)/2)
    have hp : cPayment 35 = (6952242253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 35+point (1327/200) 4096 36)/2 = (3314217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_35
  · change cPayment 36 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 36+point (1327/200) 4096 37)/2)
    have hp : cPayment 36 = (7141112093:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 36+point (1327/200) 4096 37)/2 = (3315271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_36
  · change cPayment 37 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 37+point (1327/200) 4096 38)/2)
    have hp : cPayment 37 = (7329608734:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 37+point (1327/200) 4096 38)/2 = (132653:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_37
  · change cPayment 38 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 38+point (1327/200) 4096 39)/2)
    have hp : cPayment 38 = (7517732851:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 38+point (1327/200) 4096 39)/2 = (3317379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_38
  · change cPayment 39 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 39+point (1327/200) 4096 40)/2)
    have hp : cPayment 39 = (7705485118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 39+point (1327/200) 4096 40)/2 = (3318433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_39
  · change cPayment 40 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 40+point (1327/200) 4096 41)/2)
    have hp : cPayment 40 = (7892866207:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 40+point (1327/200) 4096 41)/2 = (3319487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_40
  · change cPayment 41 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 41+point (1327/200) 4096 42)/2)
    have hp : cPayment 41 = (8079876787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 41+point (1327/200) 4096 42)/2 = (3320541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_41
  · change cPayment 42 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 42+point (1327/200) 4096 43)/2)
    have hp : cPayment 42 = (8266517528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 42+point (1327/200) 4096 43)/2 = (664319:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_42
  · change cPayment 43 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 43+point (1327/200) 4096 44)/2)
    have hp : cPayment 43 = (8452789098:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 43+point (1327/200) 4096 44)/2 = (3322649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_43
  · change cPayment 44 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 44+point (1327/200) 4096 45)/2)
    have hp : cPayment 44 = (8638692162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 44+point (1327/200) 4096 45)/2 = (3323703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_44
  · change cPayment 45 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 45+point (1327/200) 4096 46)/2)
    have hp : cPayment 45 = (8824227384:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 45+point (1327/200) 4096 46)/2 = (3324757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_45
  · change cPayment 46 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 46+point (1327/200) 4096 47)/2)
    have hp : cPayment 46 = (9009395430:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 46+point (1327/200) 4096 47)/2 = (3325811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_46
  · change cPayment 47 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 47+point (1327/200) 4096 48)/2)
    have hp : cPayment 47 = (9194196959:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 47+point (1327/200) 4096 48)/2 = (665373:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_47
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_002
