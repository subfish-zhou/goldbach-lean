import WR2ClassicalCPayments
import WR2ClassicalCPoints234
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_234 (j : Fin 16) : cPayment (16*234+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*234+j.val)+point (1327/200) 4096 (16*234+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3744 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3744+point (1327/200) 4096 3745)/2)
    have hp : cPayment 3744 = (11392348598:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3744+point (1327/200) 4096 3745)/2 = (7223503:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3744
  · change cPayment 3745 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3745+point (1327/200) 4096 3746)/2)
    have hp : cPayment 3745 = (11359357375:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3745+point (1327/200) 4096 3746)/2 = (7224557:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3745
  · change cPayment 3746 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3746+point (1327/200) 4096 3747)/2)
    have hp : cPayment 3746 = (11326369205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3746+point (1327/200) 4096 3747)/2 = (7225611:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3746
  · change cPayment 3747 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3747+point (1327/200) 4096 3748)/2)
    have hp : cPayment 3747 = (11293384090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3747+point (1327/200) 4096 3748)/2 = (1445333:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3747
  · change cPayment 3748 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3748+point (1327/200) 4096 3749)/2)
    have hp : cPayment 3748 = (11260402034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3748+point (1327/200) 4096 3749)/2 = (7227719:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3748
  · change cPayment 3749 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3749+point (1327/200) 4096 3750)/2)
    have hp : cPayment 3749 = (11227423038:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3749+point (1327/200) 4096 3750)/2 = (7228773:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3749
  · change cPayment 3750 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3750+point (1327/200) 4096 3751)/2)
    have hp : cPayment 3750 = (11194447104:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3750+point (1327/200) 4096 3751)/2 = (7229827:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3750
  · change cPayment 3751 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3751+point (1327/200) 4096 3752)/2)
    have hp : cPayment 3751 = (11161474237:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3751+point (1327/200) 4096 3752)/2 = (7230881:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3751
  · change cPayment 3752 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3752+point (1327/200) 4096 3753)/2)
    have hp : cPayment 3752 = (11128504437:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3752+point (1327/200) 4096 3753)/2 = (1446387:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3752
  · change cPayment 3753 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3753+point (1327/200) 4096 3754)/2)
    have hp : cPayment 3753 = (11095537708:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3753+point (1327/200) 4096 3754)/2 = (7232989:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3753
  · change cPayment 3754 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3754+point (1327/200) 4096 3755)/2)
    have hp : cPayment 3754 = (11062574052:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3754+point (1327/200) 4096 3755)/2 = (7234043:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3754
  · change cPayment 3755 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3755+point (1327/200) 4096 3756)/2)
    have hp : cPayment 3755 = (11029613472:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3755+point (1327/200) 4096 3756)/2 = (7235097:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3755
  · change cPayment 3756 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3756+point (1327/200) 4096 3757)/2)
    have hp : cPayment 3756 = (10996655970:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3756+point (1327/200) 4096 3757)/2 = (7236151:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3756
  · change cPayment 3757 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3757+point (1327/200) 4096 3758)/2)
    have hp : cPayment 3757 = (10963701549:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3757+point (1327/200) 4096 3758)/2 = (1447441:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3757
  · change cPayment 3758 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3758+point (1327/200) 4096 3759)/2)
    have hp : cPayment 3758 = (10930750210:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3758+point (1327/200) 4096 3759)/2 = (7238259:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3758
  · change cPayment 3759 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3759+point (1327/200) 4096 3760)/2)
    have hp : cPayment 3759 = (10897801957:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3759+point (1327/200) 4096 3760)/2 = (7239313:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3759
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_234
