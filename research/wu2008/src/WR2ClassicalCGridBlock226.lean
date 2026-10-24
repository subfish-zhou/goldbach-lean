import WR2ClassicalCPayments
import WR2ClassicalCPoints226
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_226 (j : Fin 16) : cPayment (16*226+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*226+j.val)+point (1327/200) 4096 (16*226+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3616 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3616+point (1327/200) 4096 3617)/2)
    have hp : cPayment 3616 = (15639470847:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3616+point (1327/200) 4096 3617)/2 = (7088591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3616
  · change cPayment 3617 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3617+point (1327/200) 4096 3618)/2)
    have hp : cPayment 3617 = (15606111346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3617+point (1327/200) 4096 3618)/2 = (1417929:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3617
  · change cPayment 3618 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3618+point (1327/200) 4096 3619)/2)
    have hp : cPayment 3618 = (15572754538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3618+point (1327/200) 4096 3619)/2 = (7090699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3618
  · change cPayment 3619 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3619+point (1327/200) 4096 3620)/2)
    have hp : cPayment 3619 = (15539400426:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3619+point (1327/200) 4096 3620)/2 = (7091753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3619
  · change cPayment 3620 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3620+point (1327/200) 4096 3621)/2)
    have hp : cPayment 3620 = (15506049013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3620+point (1327/200) 4096 3621)/2 = (7092807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3620
  · change cPayment 3621 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3621+point (1327/200) 4096 3622)/2)
    have hp : cPayment 3621 = (15472700302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3621+point (1327/200) 4096 3622)/2 = (7093861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3621
  · change cPayment 3622 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3622+point (1327/200) 4096 3623)/2)
    have hp : cPayment 3622 = (15439354296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3622+point (1327/200) 4096 3623)/2 = (1418983:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3622
  · change cPayment 3623 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3623+point (1327/200) 4096 3624)/2)
    have hp : cPayment 3623 = (15406010998:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3623+point (1327/200) 4096 3624)/2 = (7095969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3623
  · change cPayment 3624 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3624+point (1327/200) 4096 3625)/2)
    have hp : cPayment 3624 = (15372670411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3624+point (1327/200) 4096 3625)/2 = (7097023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3624
  · change cPayment 3625 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3625+point (1327/200) 4096 3626)/2)
    have hp : cPayment 3625 = (15339332538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3625+point (1327/200) 4096 3626)/2 = (7098077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3625
  · change cPayment 3626 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3626+point (1327/200) 4096 3627)/2)
    have hp : cPayment 3626 = (15305997383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3626+point (1327/200) 4096 3627)/2 = (7099131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3626
  · change cPayment 3627 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3627+point (1327/200) 4096 3628)/2)
    have hp : cPayment 3627 = (15272664948:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3627+point (1327/200) 4096 3628)/2 = (1420037:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3627
  · change cPayment 3628 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3628+point (1327/200) 4096 3629)/2)
    have hp : cPayment 3628 = (15239335237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3628+point (1327/200) 4096 3629)/2 = (7101239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3628
  · change cPayment 3629 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3629+point (1327/200) 4096 3630)/2)
    have hp : cPayment 3629 = (15206008251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3629+point (1327/200) 4096 3630)/2 = (7102293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3629
  · change cPayment 3630 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3630+point (1327/200) 4096 3631)/2)
    have hp : cPayment 3630 = (15172683996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3630+point (1327/200) 4096 3631)/2 = (7103347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3630
  · change cPayment 3631 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3631+point (1327/200) 4096 3632)/2)
    have hp : cPayment 3631 = (15139362473:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3631+point (1327/200) 4096 3632)/2 = (7104401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3631
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_226
