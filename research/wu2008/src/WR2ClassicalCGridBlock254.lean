import WR2ClassicalCPayments
import WR2ClassicalCPoints254
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_254 (j : Fin 16) : cPayment (16*254+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*254+j.val)+point (1327/200) 4096 (16*254+j.val+1))/2) := by
  fin_cases j
  · change cPayment 4064 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4064+point (1327/200) 4096 4065)/2)
    have hp : cPayment 4064 = (1003187240:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4064+point (1327/200) 4096 4065)/2 = (7560783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4064
  · change cPayment 4065 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4065+point (1327/200) 4096 4066)/2)
    have hp : cPayment 4065 = (971283523:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4065+point (1327/200) 4096 4066)/2 = (7561837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4065
  · change cPayment 4066 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4066+point (1327/200) 4096 4067)/2)
    have hp : cPayment 4066 = (939383498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4066+point (1327/200) 4096 4067)/2 = (7562891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4066
  · change cPayment 4067 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4067+point (1327/200) 4096 4068)/2)
    have hp : cPayment 4067 = (907487164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4067+point (1327/200) 4096 4068)/2 = (1512789:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4067
  · change cPayment 4068 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4068+point (1327/200) 4096 4069)/2)
    have hp : cPayment 4068 = (875594523:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4068+point (1327/200) 4096 4069)/2 = (7564999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4068
  · change cPayment 4069 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4069+point (1327/200) 4096 4070)/2)
    have hp : cPayment 4069 = (843705578:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4069+point (1327/200) 4096 4070)/2 = (7566053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4069
  · change cPayment 4070 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4070+point (1327/200) 4096 4071)/2)
    have hp : cPayment 4070 = (811820329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4070+point (1327/200) 4096 4071)/2 = (7567107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4070
  · change cPayment 4071 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4071+point (1327/200) 4096 4072)/2)
    have hp : cPayment 4071 = (779938778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4071+point (1327/200) 4096 4072)/2 = (7568161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4071
  · change cPayment 4072 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4072+point (1327/200) 4096 4073)/2)
    have hp : cPayment 4072 = (748060927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4072+point (1327/200) 4096 4073)/2 = (1513843:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4072
  · change cPayment 4073 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4073+point (1327/200) 4096 4074)/2)
    have hp : cPayment 4073 = (716186776:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4073+point (1327/200) 4096 4074)/2 = (7570269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4073
  · change cPayment 4074 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4074+point (1327/200) 4096 4075)/2)
    have hp : cPayment 4074 = (684316328:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4074+point (1327/200) 4096 4075)/2 = (7571323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4074
  · change cPayment 4075 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4075+point (1327/200) 4096 4076)/2)
    have hp : cPayment 4075 = (652449584:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4075+point (1327/200) 4096 4076)/2 = (7572377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4075
  · change cPayment 4076 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4076+point (1327/200) 4096 4077)/2)
    have hp : cPayment 4076 = (620586545:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4076+point (1327/200) 4096 4077)/2 = (7573431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4076
  · change cPayment 4077 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4077+point (1327/200) 4096 4078)/2)
    have hp : cPayment 4077 = (588727213:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4077+point (1327/200) 4096 4078)/2 = (1514897:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4077
  · change cPayment 4078 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4078+point (1327/200) 4096 4079)/2)
    have hp : cPayment 4078 = (556871590:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4078+point (1327/200) 4096 4079)/2 = (7575539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4078
  · change cPayment 4079 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 4079+point (1327/200) 4096 4080)/2)
    have hp : cPayment 4079 = (525019676:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 4079+point (1327/200) 4096 4080)/2 = (7576593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_4079
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_254
