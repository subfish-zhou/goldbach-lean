import WR2ClassicalCPayments
import WR2ClassicalCPoints008
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_008 (j : Fin 16) : cPayment (16*8+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*8+j.val)+point (1327/200) 4096 (16*8+j.val+1))/2) := by
  fin_cases j
  · change cPayment 128 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 128+point (1327/200) 4096 129)/2)
    have hp : cPayment 128 = (23004149071:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 128+point (1327/200) 4096 129)/2 = (3412239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_128
  · change cPayment 129 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 129+point (1327/200) 4096 130)/2)
    have hp : cPayment 129 = (23161022221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 129+point (1327/200) 4096 130)/2 = (3413293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_129
  · change cPayment 130 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 130+point (1327/200) 4096 131)/2)
    have hp : cPayment 130 = (23317579242:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 130+point (1327/200) 4096 131)/2 = (3414347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_130
  · change cPayment 131 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 131+point (1327/200) 4096 132)/2)
    have hp : cPayment 131 = (23473820691:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 131+point (1327/200) 4096 132)/2 = (3415401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_131
  · change cPayment 132 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 132+point (1327/200) 4096 133)/2)
    have hp : cPayment 132 = (23629747124:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 132+point (1327/200) 4096 133)/2 = (683291:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_132
  · change cPayment 133 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 133+point (1327/200) 4096 134)/2)
    have hp : cPayment 133 = (23785359092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 133+point (1327/200) 4096 134)/2 = (3417509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_133
  · change cPayment 134 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 134+point (1327/200) 4096 135)/2)
    have hp : cPayment 134 = (23940657150:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 134+point (1327/200) 4096 135)/2 = (3418563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_134
  · change cPayment 135 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 135+point (1327/200) 4096 136)/2)
    have hp : cPayment 135 = (24095641848:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 135+point (1327/200) 4096 136)/2 = (3419617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_135
  · change cPayment 136 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 136+point (1327/200) 4096 137)/2)
    have hp : cPayment 136 = (24250313738:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 136+point (1327/200) 4096 137)/2 = (3420671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_136
  · change cPayment 137 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 137+point (1327/200) 4096 138)/2)
    have hp : cPayment 137 = (24404673367:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 137+point (1327/200) 4096 138)/2 = (136869:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_137
  · change cPayment 138 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 138+point (1327/200) 4096 139)/2)
    have hp : cPayment 138 = (24558721285:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 138+point (1327/200) 4096 139)/2 = (3422779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_138
  · change cPayment 139 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 139+point (1327/200) 4096 140)/2)
    have hp : cPayment 139 = (24712458038:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 139+point (1327/200) 4096 140)/2 = (3423833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_139
  · change cPayment 140 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 140+point (1327/200) 4096 141)/2)
    have hp : cPayment 140 = (24865884172:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 140+point (1327/200) 4096 141)/2 = (3424887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_140
  · change cPayment 141 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 141+point (1327/200) 4096 142)/2)
    have hp : cPayment 141 = (25019000232:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 141+point (1327/200) 4096 142)/2 = (3425941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_141
  · change cPayment 142 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 142+point (1327/200) 4096 143)/2)
    have hp : cPayment 142 = (25171806762:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 142+point (1327/200) 4096 143)/2 = (685399:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_142
  · change cPayment 143 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 143+point (1327/200) 4096 144)/2)
    have hp : cPayment 143 = (25324304304:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 143+point (1327/200) 4096 144)/2 = (3428049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_143
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_008
