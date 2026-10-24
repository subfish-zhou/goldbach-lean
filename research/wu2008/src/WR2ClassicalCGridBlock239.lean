import WR2ClassicalCPayments
import WR2ClassicalCPoints239
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_239 (j : Fin 16) : cPayment (16*239+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*239+j.val)+point (1327/200) 4096 (16*239+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3824 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3824+point (1327/200) 4096 3825)/2)
    have hp : cPayment 3824 = (8762900876:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3824+point (1327/200) 4096 3825)/2 = (7307823:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3824
  · change cPayment 3825 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3825+point (1327/200) 4096 3826)/2)
    have hp : cPayment 3825 = (8730161612:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3825+point (1327/200) 4096 3826)/2 = (7308877:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3825
  · change cPayment 3826 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3826+point (1327/200) 4096 3827)/2)
    have hp : cPayment 3826 = (8697425592:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3826+point (1327/200) 4096 3827)/2 = (7309931:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3826
  · change cPayment 3827 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3827+point (1327/200) 4096 3828)/2)
    have hp : cPayment 3827 = (8664692820:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3827+point (1327/200) 4096 3828)/2 = (1462197:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3827
  · change cPayment 3828 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3828+point (1327/200) 4096 3829)/2)
    have hp : cPayment 3828 = (8631963296:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3828+point (1327/200) 4096 3829)/2 = (7312039:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3828
  · change cPayment 3829 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3829+point (1327/200) 4096 3830)/2)
    have hp : cPayment 3829 = (8599237024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3829+point (1327/200) 4096 3830)/2 = (7313093:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3829
  · change cPayment 3830 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3830+point (1327/200) 4096 3831)/2)
    have hp : cPayment 3830 = (8566514005:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3830+point (1327/200) 4096 3831)/2 = (7314147:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3830
  · change cPayment 3831 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3831+point (1327/200) 4096 3832)/2)
    have hp : cPayment 3831 = (8533794242:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3831+point (1327/200) 4096 3832)/2 = (7315201:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3831
  · change cPayment 3832 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3832+point (1327/200) 4096 3833)/2)
    have hp : cPayment 3832 = (8501077736:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3832+point (1327/200) 4096 3833)/2 = (1463251:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3832
  · change cPayment 3833 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3833+point (1327/200) 4096 3834)/2)
    have hp : cPayment 3833 = (8468364491:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3833+point (1327/200) 4096 3834)/2 = (7317309:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3833
  · change cPayment 3834 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3834+point (1327/200) 4096 3835)/2)
    have hp : cPayment 3834 = (8435654509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3834+point (1327/200) 4096 3835)/2 = (7318363:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3834
  · change cPayment 3835 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3835+point (1327/200) 4096 3836)/2)
    have hp : cPayment 3835 = (8402947791:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3835+point (1327/200) 4096 3836)/2 = (7319417:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3835
  · change cPayment 3836 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3836+point (1327/200) 4096 3837)/2)
    have hp : cPayment 3836 = (8370244340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3836+point (1327/200) 4096 3837)/2 = (7320471:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3836
  · change cPayment 3837 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3837+point (1327/200) 4096 3838)/2)
    have hp : cPayment 3837 = (8337544157:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3837+point (1327/200) 4096 3838)/2 = (292861:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3837
  · change cPayment 3838 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3838+point (1327/200) 4096 3839)/2)
    have hp : cPayment 3838 = (8304847247:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3838+point (1327/200) 4096 3839)/2 = (7322579:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3838
  · change cPayment 3839 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3839+point (1327/200) 4096 3840)/2)
    have hp : cPayment 3839 = (8272153609:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3839+point (1327/200) 4096 3840)/2 = (7323633:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3839
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_239
