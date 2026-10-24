import WR2ClassicalCPayments
import WR2ClassicalCPoints187
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_187 (j : Fin 16) : cPayment (16*187+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*187+j.val)+point (1327/200) 4096 (16*187+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2992 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2992+point (1327/200) 4096 2993)/2)
    have hp : cPayment 2992 = (36820728217:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2992+point (1327/200) 4096 2993)/2 = (1286179:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2992
  · change cPayment 2993 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2993+point (1327/200) 4096 2994)/2)
    have hp : cPayment 2993 = (36786519846:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2993+point (1327/200) 4096 2994)/2 = (6431949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2993
  · change cPayment 2994 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2994+point (1327/200) 4096 2995)/2)
    have hp : cPayment 2994 = (36752311064:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2994+point (1327/200) 4096 2995)/2 = (6433003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2994
  · change cPayment 2995 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2995+point (1327/200) 4096 2996)/2)
    have hp : cPayment 2995 = (36718101880:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2995+point (1327/200) 4096 2996)/2 = (6434057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2995
  · change cPayment 2996 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2996+point (1327/200) 4096 2997)/2)
    have hp : cPayment 2996 = (36683892299:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2996+point (1327/200) 4096 2997)/2 = (6435111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2996
  · change cPayment 2997 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2997+point (1327/200) 4096 2998)/2)
    have hp : cPayment 2997 = (36649682330:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2997+point (1327/200) 4096 2998)/2 = (1287233:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2997
  · change cPayment 2998 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2998+point (1327/200) 4096 2999)/2)
    have hp : cPayment 2998 = (36615471980:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2998+point (1327/200) 4096 2999)/2 = (6437219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2998
  · change cPayment 2999 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2999+point (1327/200) 4096 3000)/2)
    have hp : cPayment 2999 = (36581261256:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2999+point (1327/200) 4096 3000)/2 = (6438273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2999
  · change cPayment 3000 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3000+point (1327/200) 4096 3001)/2)
    have hp : cPayment 3000 = (36547050166:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3000+point (1327/200) 4096 3001)/2 = (6439327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3000
  · change cPayment 3001 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3001+point (1327/200) 4096 3002)/2)
    have hp : cPayment 3001 = (36512838716:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3001+point (1327/200) 4096 3002)/2 = (6440381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3001
  · change cPayment 3002 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3002+point (1327/200) 4096 3003)/2)
    have hp : cPayment 3002 = (36478626916:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3002+point (1327/200) 4096 3003)/2 = (1288287:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3002
  · change cPayment 3003 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3003+point (1327/200) 4096 3004)/2)
    have hp : cPayment 3003 = (36444414770:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3003+point (1327/200) 4096 3004)/2 = (6442489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3003
  · change cPayment 3004 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3004+point (1327/200) 4096 3005)/2)
    have hp : cPayment 3004 = (36410202288:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3004+point (1327/200) 4096 3005)/2 = (6443543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3004
  · change cPayment 3005 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3005+point (1327/200) 4096 3006)/2)
    have hp : cPayment 3005 = (36375989476:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3005+point (1327/200) 4096 3006)/2 = (6444597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3005
  · change cPayment 3006 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3006+point (1327/200) 4096 3007)/2)
    have hp : cPayment 3006 = (36341776341:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3006+point (1327/200) 4096 3007)/2 = (6445651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3006
  · change cPayment 3007 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3007+point (1327/200) 4096 3008)/2)
    have hp : cPayment 3007 = (36307562892:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3007+point (1327/200) 4096 3008)/2 = (1289341:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3007
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_187
