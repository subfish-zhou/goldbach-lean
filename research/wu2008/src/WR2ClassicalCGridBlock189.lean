import WR2ClassicalCPayments
import WR2ClassicalCPoints189
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_189 (j : Fin 16) : cPayment (16*189+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*189+j.val)+point (1327/200) 4096 (16*189+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3024 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3024+point (1327/200) 4096 3025)/2)
    have hp : cPayment 3024 = (35725893030:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3024+point (1327/200) 4096 3025)/2 = (6464623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3024
  · change cPayment 3025 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3025+point (1327/200) 4096 3026)/2)
    have hp : cPayment 3025 = (35691675141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3025+point (1327/200) 4096 3026)/2 = (6465677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3025
  · change cPayment 3026 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3026+point (1327/200) 4096 3027)/2)
    have hp : cPayment 3026 = (35657457073:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3026+point (1327/200) 4096 3027)/2 = (6466731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3026
  · change cPayment 3027 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3027+point (1327/200) 4096 3028)/2)
    have hp : cPayment 3027 = (35623238833:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3027+point (1327/200) 4096 3028)/2 = (1293557:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3027
  · change cPayment 3028 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3028+point (1327/200) 4096 3029)/2)
    have hp : cPayment 3028 = (35589020429:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3028+point (1327/200) 4096 3029)/2 = (6468839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3028
  · change cPayment 3029 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3029+point (1327/200) 4096 3030)/2)
    have hp : cPayment 3029 = (35554801867:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3029+point (1327/200) 4096 3030)/2 = (6469893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3029
  · change cPayment 3030 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3030+point (1327/200) 4096 3031)/2)
    have hp : cPayment 3030 = (35520583155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3030+point (1327/200) 4096 3031)/2 = (6470947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3030
  · change cPayment 3031 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3031+point (1327/200) 4096 3032)/2)
    have hp : cPayment 3031 = (35486364300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3031+point (1327/200) 4096 3032)/2 = (6472001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3031
  · change cPayment 3032 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3032+point (1327/200) 4096 3033)/2)
    have hp : cPayment 3032 = (35452145308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3032+point (1327/200) 4096 3033)/2 = (1294611:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3032
  · change cPayment 3033 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3033+point (1327/200) 4096 3034)/2)
    have hp : cPayment 3033 = (35417926187:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3033+point (1327/200) 4096 3034)/2 = (6474109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3033
  · change cPayment 3034 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3034+point (1327/200) 4096 3035)/2)
    have hp : cPayment 3034 = (35383706944:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3034+point (1327/200) 4096 3035)/2 = (6475163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3034
  · change cPayment 3035 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3035+point (1327/200) 4096 3036)/2)
    have hp : cPayment 3035 = (35349487585:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3035+point (1327/200) 4096 3036)/2 = (6476217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3035
  · change cPayment 3036 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3036+point (1327/200) 4096 3037)/2)
    have hp : cPayment 3036 = (35315268118:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3036+point (1327/200) 4096 3037)/2 = (6477271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3036
  · change cPayment 3037 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3037+point (1327/200) 4096 3038)/2)
    have hp : cPayment 3037 = (35281048550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3037+point (1327/200) 4096 3038)/2 = (259133:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3037
  · change cPayment 3038 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3038+point (1327/200) 4096 3039)/2)
    have hp : cPayment 3038 = (35246828888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3038+point (1327/200) 4096 3039)/2 = (6479379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3038
  · change cPayment 3039 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3039+point (1327/200) 4096 3040)/2)
    have hp : cPayment 3039 = (35212609138:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3039+point (1327/200) 4096 3040)/2 = (6480433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3039
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_189
