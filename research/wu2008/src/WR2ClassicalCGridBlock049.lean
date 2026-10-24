import WR2ClassicalCPayments
import WR2ClassicalCPoints049
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_049 (j : Fin 16) : cPayment (16*49+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*49+j.val)+point (1327/200) 4096 (16*49+j.val+1))/2) := by
  fin_cases j
  · change cPayment 784 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 784+point (1327/200) 4096 785)/2)
    have hp : cPayment 784 = (77468405363:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 784+point (1327/200) 4096 785)/2 = (4103663:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_784
  · change cPayment 785 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 785+point (1327/200) 4096 786)/2)
    have hp : cPayment 785 = (77499574860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 785+point (1327/200) 4096 786)/2 = (4104717:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_785
  · change cPayment 786 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 786+point (1327/200) 4096 787)/2)
    have hp : cPayment 786 = (77530636659:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 786+point (1327/200) 4096 787)/2 = (4105771:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_786
  · change cPayment 787 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 787+point (1327/200) 4096 788)/2)
    have hp : cPayment 787 = (77561590927:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 787+point (1327/200) 4096 788)/2 = (164273:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_787
  · change cPayment 788 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 788+point (1327/200) 4096 789)/2)
    have hp : cPayment 788 = (77592437832:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 788+point (1327/200) 4096 789)/2 = (4107879:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_788
  · change cPayment 789 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 789+point (1327/200) 4096 790)/2)
    have hp : cPayment 789 = (77623177541:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 789+point (1327/200) 4096 790)/2 = (4108933:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_789
  · change cPayment 790 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 790+point (1327/200) 4096 791)/2)
    have hp : cPayment 790 = (77653810222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 790+point (1327/200) 4096 791)/2 = (4109987:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_790
  · change cPayment 791 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 791+point (1327/200) 4096 792)/2)
    have hp : cPayment 791 = (77684336040:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 791+point (1327/200) 4096 792)/2 = (4111041:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_791
  · change cPayment 792 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 792+point (1327/200) 4096 793)/2)
    have hp : cPayment 792 = (77714755162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 792+point (1327/200) 4096 793)/2 = (822419:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_792
  · change cPayment 793 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 793+point (1327/200) 4096 794)/2)
    have hp : cPayment 793 = (77745067755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 793+point (1327/200) 4096 794)/2 = (4113149:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_793
  · change cPayment 794 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 794+point (1327/200) 4096 795)/2)
    have hp : cPayment 794 = (77775273983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 794+point (1327/200) 4096 795)/2 = (4114203:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_794
  · change cPayment 795 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 795+point (1327/200) 4096 796)/2)
    have hp : cPayment 795 = (77805374013:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 795+point (1327/200) 4096 796)/2 = (4115257:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_795
  · change cPayment 796 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 796+point (1327/200) 4096 797)/2)
    have hp : cPayment 796 = (77835368010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 796+point (1327/200) 4096 797)/2 = (4116311:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_796
  · change cPayment 797 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 797+point (1327/200) 4096 798)/2)
    have hp : cPayment 797 = (77865256139:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 797+point (1327/200) 4096 798)/2 = (823473:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_797
  · change cPayment 798 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 798+point (1327/200) 4096 799)/2)
    have hp : cPayment 798 = (77895038564:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 798+point (1327/200) 4096 799)/2 = (4118419:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_798
  · change cPayment 799 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 799+point (1327/200) 4096 800)/2)
    have hp : cPayment 799 = (77924715451:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 799+point (1327/200) 4096 800)/2 = (4119473:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_799
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_049
