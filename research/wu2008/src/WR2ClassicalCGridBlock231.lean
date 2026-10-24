import WR2ClassicalCPayments
import WR2ClassicalCPoints231
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_231 (j : Fin 16) : cPayment (16*231+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*231+j.val)+point (1327/200) 4096 (16*231+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3696 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3696+point (1327/200) 4096 3697)/2)
    have hp : cPayment 3696 = (12979466533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3696+point (1327/200) 4096 3697)/2 = (7172911:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3696
  · change cPayment 3697 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3697+point (1327/200) 4096 3698)/2)
    have hp : cPayment 3697 = (12946331847:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3697+point (1327/200) 4096 3698)/2 = (1434793:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3697
  · change cPayment 3698 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3698+point (1327/200) 4096 3699)/2)
    have hp : cPayment 3698 = (12913200086:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3698+point (1327/200) 4096 3699)/2 = (7175019:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3698
  · change cPayment 3699 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3699+point (1327/200) 4096 3700)/2)
    have hp : cPayment 3699 = (12880071254:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3699+point (1327/200) 4096 3700)/2 = (7176073:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3699
  · change cPayment 3700 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3700+point (1327/200) 4096 3701)/2)
    have hp : cPayment 3700 = (12846945354:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3700+point (1327/200) 4096 3701)/2 = (7177127:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3700
  · change cPayment 3701 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3701+point (1327/200) 4096 3702)/2)
    have hp : cPayment 3701 = (12813822387:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3701+point (1327/200) 4096 3702)/2 = (7178181:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3701
  · change cPayment 3702 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3702+point (1327/200) 4096 3703)/2)
    have hp : cPayment 3702 = (12780702357:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3702+point (1327/200) 4096 3703)/2 = (1435847:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3702
  · change cPayment 3703 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3703+point (1327/200) 4096 3704)/2)
    have hp : cPayment 3703 = (12747585267:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3703+point (1327/200) 4096 3704)/2 = (7180289:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3703
  · change cPayment 3704 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3704+point (1327/200) 4096 3705)/2)
    have hp : cPayment 3704 = (12714471120:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3704+point (1327/200) 4096 3705)/2 = (7181343:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3704
  · change cPayment 3705 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3705+point (1327/200) 4096 3706)/2)
    have hp : cPayment 3705 = (12681359917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3705+point (1327/200) 4096 3706)/2 = (7182397:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3705
  · change cPayment 3706 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3706+point (1327/200) 4096 3707)/2)
    have hp : cPayment 3706 = (12648251662:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3706+point (1327/200) 4096 3707)/2 = (7183451:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3706
  · change cPayment 3707 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3707+point (1327/200) 4096 3708)/2)
    have hp : cPayment 3707 = (12615146357:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3707+point (1327/200) 4096 3708)/2 = (1436901:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3707
  · change cPayment 3708 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3708+point (1327/200) 4096 3709)/2)
    have hp : cPayment 3708 = (12582044005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3708+point (1327/200) 4096 3709)/2 = (7185559:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3708
  · change cPayment 3709 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3709+point (1327/200) 4096 3710)/2)
    have hp : cPayment 3709 = (12548944610:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3709+point (1327/200) 4096 3710)/2 = (7186613:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3709
  · change cPayment 3710 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3710+point (1327/200) 4096 3711)/2)
    have hp : cPayment 3710 = (12515848172:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3710+point (1327/200) 4096 3711)/2 = (7187667:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3710
  · change cPayment 3711 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3711+point (1327/200) 4096 3712)/2)
    have hp : cPayment 3711 = (12482754696:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3711+point (1327/200) 4096 3712)/2 = (7188721:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3711
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_231
