import WR2ClassicalCPayments
import WR2ClassicalCPoints243
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_243 (j : Fin 16) : cPayment (16*243+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*243+j.val)+point (1327/200) 4096 (16*243+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3888 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3888+point (1327/200) 4096 3889)/2)
    have hp : cPayment 3888 = (6674220313:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3888+point (1327/200) 4096 3889)/2 = (7375279:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3888
  · change cPayment 3889 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3889+point (1327/200) 4096 3890)/2)
    have hp : cPayment 3889 = (6641693082:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3889+point (1327/200) 4096 3890)/2 = (7376333:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3889
  · change cPayment 3890 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3890+point (1327/200) 4096 3891)/2)
    have hp : cPayment 3890 = (6609169232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3890+point (1327/200) 4096 3891)/2 = (7377387:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3890
  · change cPayment 3891 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3891+point (1327/200) 4096 3892)/2)
    have hp : cPayment 3891 = (6576648765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3891+point (1327/200) 4096 3892)/2 = (7378441:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3891
  · change cPayment 3892 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3892+point (1327/200) 4096 3893)/2)
    have hp : cPayment 3892 = (6544131684:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3892+point (1327/200) 4096 3893)/2 = (1475899:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3892
  · change cPayment 3893 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3893+point (1327/200) 4096 3894)/2)
    have hp : cPayment 3893 = (6511617990:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3893+point (1327/200) 4096 3894)/2 = (7380549:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3893
  · change cPayment 3894 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3894+point (1327/200) 4096 3895)/2)
    have hp : cPayment 3894 = (6479107686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3894+point (1327/200) 4096 3895)/2 = (7381603:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3894
  · change cPayment 3895 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3895+point (1327/200) 4096 3896)/2)
    have hp : cPayment 3895 = (6446600773:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3895+point (1327/200) 4096 3896)/2 = (7382657:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3895
  · change cPayment 3896 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3896+point (1327/200) 4096 3897)/2)
    have hp : cPayment 3896 = (6414097253:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3896+point (1327/200) 4096 3897)/2 = (7383711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3896
  · change cPayment 3897 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3897+point (1327/200) 4096 3898)/2)
    have hp : cPayment 3897 = (6381597129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3897+point (1327/200) 4096 3898)/2 = (1476953:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3897
  · change cPayment 3898 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3898+point (1327/200) 4096 3899)/2)
    have hp : cPayment 3898 = (6349100402:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3898+point (1327/200) 4096 3899)/2 = (7385819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3898
  · change cPayment 3899 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3899+point (1327/200) 4096 3900)/2)
    have hp : cPayment 3899 = (6316607075:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3899+point (1327/200) 4096 3900)/2 = (7386873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3899
  · change cPayment 3900 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3900+point (1327/200) 4096 3901)/2)
    have hp : cPayment 3900 = (6284117149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3900+point (1327/200) 4096 3901)/2 = (7387927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3900
  · change cPayment 3901 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3901+point (1327/200) 4096 3902)/2)
    have hp : cPayment 3901 = (6251630626:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3901+point (1327/200) 4096 3902)/2 = (7388981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3901
  · change cPayment 3902 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3902+point (1327/200) 4096 3903)/2)
    have hp : cPayment 3902 = (6219147509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3902+point (1327/200) 4096 3903)/2 = (1478007:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3902
  · change cPayment 3903 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3903+point (1327/200) 4096 3904)/2)
    have hp : cPayment 3903 = (6186667799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3903+point (1327/200) 4096 3904)/2 = (7391089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3903
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_243
