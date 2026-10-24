import WR2ClassicalCPayments
import WR2ClassicalCPoints006
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_006 (j : Fin 16) : cPayment (16*6+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*6+j.val)+point (1327/200) 4096 (16*6+j.val+1))/2) := by
  fin_cases j
  · change cPayment 96 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 96+point (1327/200) 4096 97)/2)
    have hp : cPayment 96 = (17813905219:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 96+point (1327/200) 4096 97)/2 = (3378511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_96
  · change cPayment 97 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 97+point (1327/200) 4096 98)/2)
    have hp : cPayment 97 = (17981194958:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 97+point (1327/200) 4096 98)/2 = (675913:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_97
  · change cPayment 98 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 98+point (1327/200) 4096 99)/2)
    have hp : cPayment 98 = (18148150162:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 98+point (1327/200) 4096 99)/2 = (3380619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_98
  · change cPayment 99 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 99+point (1327/200) 4096 100)/2)
    have hp : cPayment 99 = (18314771425:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 99+point (1327/200) 4096 100)/2 = (3381673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_99
  · change cPayment 100 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 100+point (1327/200) 4096 101)/2)
    have hp : cPayment 100 = (18481059340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 100+point (1327/200) 4096 101)/2 = (3382727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_100
  · change cPayment 101 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 101+point (1327/200) 4096 102)/2)
    have hp : cPayment 101 = (18647014497:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 101+point (1327/200) 4096 102)/2 = (3383781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_101
  · change cPayment 102 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 102+point (1327/200) 4096 103)/2)
    have hp : cPayment 102 = (18812637486:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 102+point (1327/200) 4096 103)/2 = (676967:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_102
  · change cPayment 103 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 103+point (1327/200) 4096 104)/2)
    have hp : cPayment 103 = (18977928898:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 103+point (1327/200) 4096 104)/2 = (3385889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_103
  · change cPayment 104 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 104+point (1327/200) 4096 105)/2)
    have hp : cPayment 104 = (19142889318:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 104+point (1327/200) 4096 105)/2 = (3386943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_104
  · change cPayment 105 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 105+point (1327/200) 4096 106)/2)
    have hp : cPayment 105 = (19307519334:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 105+point (1327/200) 4096 106)/2 = (3387997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_105
  · change cPayment 106 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 106+point (1327/200) 4096 107)/2)
    have hp : cPayment 106 = (19471819531:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 106+point (1327/200) 4096 107)/2 = (3389051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_106
  · change cPayment 107 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 107+point (1327/200) 4096 108)/2)
    have hp : cPayment 107 = (19635790493:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 107+point (1327/200) 4096 108)/2 = (678021:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_107
  · change cPayment 108 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 108+point (1327/200) 4096 109)/2)
    have hp : cPayment 108 = (19799432803:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 108+point (1327/200) 4096 109)/2 = (3391159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_108
  · change cPayment 109 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 109+point (1327/200) 4096 110)/2)
    have hp : cPayment 109 = (19962747042:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 109+point (1327/200) 4096 110)/2 = (3392213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_109
  · change cPayment 110 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 110+point (1327/200) 4096 111)/2)
    have hp : cPayment 110 = (20125733791:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 110+point (1327/200) 4096 111)/2 = (3393267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_110
  · change cPayment 111 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 111+point (1327/200) 4096 112)/2)
    have hp : cPayment 111 = (20288393629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 111+point (1327/200) 4096 112)/2 = (3394321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_111
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_006
