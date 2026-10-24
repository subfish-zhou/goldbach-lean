import WR2ClassicalCPayments
import WR2ClassicalCPoints236
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_236 (j : Fin 16) : cPayment (16*236+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*236+j.val)+point (1327/200) 4096 (16*236+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3776 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3776+point (1327/200) 4096 3777)/2)
    have hp : cPayment 3776 = (10338156169:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3776+point (1327/200) 4096 3777)/2 = (7257231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3776
  · change cPayment 3777 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3777+point (1327/200) 4096 3778)/2)
    have hp : cPayment 3777 = (10305263881:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3777+point (1327/200) 4096 3778)/2 = (1451657:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3777
  · change cPayment 3778 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3778+point (1327/200) 4096 3779)/2)
    have hp : cPayment 3778 = (10272374725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3778+point (1327/200) 4096 3779)/2 = (7259339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3778
  · change cPayment 3779 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3779+point (1327/200) 4096 3780)/2)
    have hp : cPayment 3779 = (10239488704:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3779+point (1327/200) 4096 3780)/2 = (7260393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3779
  · change cPayment 3780 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3780+point (1327/200) 4096 3781)/2)
    have hp : cPayment 3780 = (10206605821:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3780+point (1327/200) 4096 3781)/2 = (7261447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3780
  · change cPayment 3781 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3781+point (1327/200) 4096 3782)/2)
    have hp : cPayment 3781 = (10173726077:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3781+point (1327/200) 4096 3782)/2 = (7262501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3781
  · change cPayment 3782 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3782+point (1327/200) 4096 3783)/2)
    have hp : cPayment 3782 = (10140849475:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3782+point (1327/200) 4096 3783)/2 = (1452711:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3782
  · change cPayment 3783 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3783+point (1327/200) 4096 3784)/2)
    have hp : cPayment 3783 = (10107976017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3783+point (1327/200) 4096 3784)/2 = (7264609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3783
  · change cPayment 3784 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3784+point (1327/200) 4096 3785)/2)
    have hp : cPayment 3784 = (10075105707:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3784+point (1327/200) 4096 3785)/2 = (7265663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3784
  · change cPayment 3785 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3785+point (1327/200) 4096 3786)/2)
    have hp : cPayment 3785 = (10042238546:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3785+point (1327/200) 4096 3786)/2 = (7266717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3785
  · change cPayment 3786 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3786+point (1327/200) 4096 3787)/2)
    have hp : cPayment 3786 = (10009374536:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3786+point (1327/200) 4096 3787)/2 = (7267771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3786
  · change cPayment 3787 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3787+point (1327/200) 4096 3788)/2)
    have hp : cPayment 3787 = (9976513681:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3787+point (1327/200) 4096 3788)/2 = (290753:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3787
  · change cPayment 3788 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3788+point (1327/200) 4096 3789)/2)
    have hp : cPayment 3788 = (9943655982:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3788+point (1327/200) 4096 3789)/2 = (7269879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3788
  · change cPayment 3789 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3789+point (1327/200) 4096 3790)/2)
    have hp : cPayment 3789 = (9910801442:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3789+point (1327/200) 4096 3790)/2 = (7270933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3789
  · change cPayment 3790 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3790+point (1327/200) 4096 3791)/2)
    have hp : cPayment 3790 = (9877950063:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3790+point (1327/200) 4096 3791)/2 = (7271987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3790
  · change cPayment 3791 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3791+point (1327/200) 4096 3792)/2)
    have hp : cPayment 3791 = (9845101848:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3791+point (1327/200) 4096 3792)/2 = (7273041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3791
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_236
