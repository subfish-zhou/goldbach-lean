import WR2ClassicalCPayments
import WR2ClassicalCPoints000
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_000 (j : Fin 16) : cPayment (16*0+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*0+j.val)+point (1327/200) 4096 (16*0+j.val+1))/2) := by
  fin_cases j
  · change cPayment 0 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 0+point (1327/200) 4096 1)/2)
    have hp : cPayment 0 = (101333468:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 0+point (1327/200) 4096 1)/2 = (3277327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_0
  · change cPayment 1 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1+point (1327/200) 4096 2)/2)
    have hp : cPayment 1 = (303701644:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1+point (1327/200) 4096 2)/2 = (3278381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1
  · change cPayment 2 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2+point (1327/200) 4096 3)/2)
    have hp : cPayment 2 = (505672080:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2+point (1327/200) 4096 3)/2 = (655887:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2
  · change cPayment 3 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3+point (1327/200) 4096 4)/2)
    have hp : cPayment 3 = (707245503:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3+point (1327/200) 4096 4)/2 = (3280489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3
  · change cPayment 4 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4+point (1327/200) 4096 5)/2)
    have hp : cPayment 4 = (908422639:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4+point (1327/200) 4096 5)/2 = (3281543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4
  · change cPayment 5 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 5+point (1327/200) 4096 6)/2)
    have hp : cPayment 5 = (1109204211:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 5+point (1327/200) 4096 6)/2 = (3282597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_5
  · change cPayment 6 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 6+point (1327/200) 4096 7)/2)
    have hp : cPayment 6 = (1309590942:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 6+point (1327/200) 4096 7)/2 = (3283651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_6
  · change cPayment 7 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 7+point (1327/200) 4096 8)/2)
    have hp : cPayment 7 = (1509583553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 7+point (1327/200) 4096 8)/2 = (656941:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_7
  · change cPayment 8 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 8+point (1327/200) 4096 9)/2)
    have hp : cPayment 8 = (1709182763:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 8+point (1327/200) 4096 9)/2 = (3285759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_8
  · change cPayment 9 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 9+point (1327/200) 4096 10)/2)
    have hp : cPayment 9 = (1908389289:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 9+point (1327/200) 4096 10)/2 = (3286813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_9
  · change cPayment 10 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 10+point (1327/200) 4096 11)/2)
    have hp : cPayment 10 = (2107203849:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 10+point (1327/200) 4096 11)/2 = (3287867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_10
  · change cPayment 11 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 11+point (1327/200) 4096 12)/2)
    have hp : cPayment 11 = (2305627155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 11+point (1327/200) 4096 12)/2 = (3288921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_11
  · change cPayment 12 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 12+point (1327/200) 4096 13)/2)
    have hp : cPayment 12 = (2503659923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 12+point (1327/200) 4096 13)/2 = (131599:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_12
  · change cPayment 13 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 13+point (1327/200) 4096 14)/2)
    have hp : cPayment 13 = (2701302862:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 13+point (1327/200) 4096 14)/2 = (3291029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_13
  · change cPayment 14 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 14+point (1327/200) 4096 15)/2)
    have hp : cPayment 14 = (2898556684:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 14+point (1327/200) 4096 15)/2 = (3292083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_14
  · change cPayment 15 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 15+point (1327/200) 4096 16)/2)
    have hp : cPayment 15 = (3095422096:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 15+point (1327/200) 4096 16)/2 = (3293137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_15
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_000
