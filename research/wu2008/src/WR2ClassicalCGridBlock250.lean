import WR2ClassicalCPayments
import WR2ClassicalCPoints250
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_250 (j : Fin 16) : cPayment (16*250+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*250+j.val)+point (1327/200) 4096 (16*250+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4000 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4000+point (1327/200) 4096 4001)/2)
    have hp : cPayment 4000 = (3052630456:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4000+point (1327/200) 4096 4001)/2 = (7493327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4000
  · change cPayment 4001 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4001+point (1327/200) 4096 4002)/2)
    have hp : cPayment 4001 = (3020493799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4001+point (1327/200) 4096 4002)/2 = (7494381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4001
  · change cPayment 4002 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4002+point (1327/200) 4096 4003)/2)
    have hp : cPayment 4002 = (2988360730:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4002+point (1327/200) 4096 4003)/2 = (1499087:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4002
  · change cPayment 4003 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4003+point (1327/200) 4096 4004)/2)
    have hp : cPayment 4003 = (2956231251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4003+point (1327/200) 4096 4004)/2 = (7496489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4003
  · change cPayment 4004 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4004+point (1327/200) 4096 4005)/2)
    have hp : cPayment 4004 = (2924105365:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4004+point (1327/200) 4096 4005)/2 = (7497543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4004
  · change cPayment 4005 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4005+point (1327/200) 4096 4006)/2)
    have hp : cPayment 4005 = (2891983072:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4005+point (1327/200) 4096 4006)/2 = (7498597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4005
  · change cPayment 4006 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4006+point (1327/200) 4096 4007)/2)
    have hp : cPayment 4006 = (2859864374:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4006+point (1327/200) 4096 4007)/2 = (7499651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4006
  · change cPayment 4007 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4007+point (1327/200) 4096 4008)/2)
    have hp : cPayment 4007 = (2827749274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4007+point (1327/200) 4096 4008)/2 = (1500141:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4007
  · change cPayment 4008 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4008+point (1327/200) 4096 4009)/2)
    have hp : cPayment 4008 = (2795637772:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4008+point (1327/200) 4096 4009)/2 = (7501759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4008
  · change cPayment 4009 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4009+point (1327/200) 4096 4010)/2)
    have hp : cPayment 4009 = (2763529870:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4009+point (1327/200) 4096 4010)/2 = (7502813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4009
  · change cPayment 4010 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4010+point (1327/200) 4096 4011)/2)
    have hp : cPayment 4010 = (2731425570:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4010+point (1327/200) 4096 4011)/2 = (7503867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4010
  · change cPayment 4011 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4011+point (1327/200) 4096 4012)/2)
    have hp : cPayment 4011 = (2699324874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4011+point (1327/200) 4096 4012)/2 = (7504921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4011
  · change cPayment 4012 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4012+point (1327/200) 4096 4013)/2)
    have hp : cPayment 4012 = (2667227784:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4012+point (1327/200) 4096 4013)/2 = (300239:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4012
  · change cPayment 4013 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4013+point (1327/200) 4096 4014)/2)
    have hp : cPayment 4013 = (2635134300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4013+point (1327/200) 4096 4014)/2 = (7507029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4013
  · change cPayment 4014 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4014+point (1327/200) 4096 4015)/2)
    have hp : cPayment 4014 = (2603044425:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4014+point (1327/200) 4096 4015)/2 = (7508083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4014
  · change cPayment 4015 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4015+point (1327/200) 4096 4016)/2)
    have hp : cPayment 4015 = (2570958160:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4015+point (1327/200) 4096 4016)/2 = (7509137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4015
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_250
