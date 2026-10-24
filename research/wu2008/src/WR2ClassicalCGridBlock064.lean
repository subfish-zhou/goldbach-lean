import WR2ClassicalCPayments
import WR2ClassicalCPoints064
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_064 (j : Fin 16) : cPayment (16*64+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*64+j.val)+point (1327/200) 4096 (16*64+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1024 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1024+point (1327/200) 4096 1025)/2)
    have hp : cPayment 1024 = (82207658190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1024+point (1327/200) 4096 1025)/2 = (4356623:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1024
  · change cPayment 1025 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1025+point (1327/200) 4096 1026)/2)
    have hp : cPayment 1025 = (82217224159:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1025+point (1327/200) 4096 1026)/2 = (4357677:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1025
  · change cPayment 1026 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1026+point (1327/200) 4096 1027)/2)
    have hp : cPayment 1026 = (82226715791:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1026+point (1327/200) 4096 1027)/2 = (4358731:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1026
  · change cPayment 1027 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1027+point (1327/200) 4096 1028)/2)
    have hp : cPayment 1027 = (82236133199:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1027+point (1327/200) 4096 1028)/2 = (871957:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1027
  · change cPayment 1028 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1028+point (1327/200) 4096 1029)/2)
    have hp : cPayment 1028 = (82245476498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1028+point (1327/200) 4096 1029)/2 = (4360839:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1028
  · change cPayment 1029 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1029+point (1327/200) 4096 1030)/2)
    have hp : cPayment 1029 = (82254745802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1029+point (1327/200) 4096 1030)/2 = (4361893:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1029
  · change cPayment 1030 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1030+point (1327/200) 4096 1031)/2)
    have hp : cPayment 1030 = (82263941222:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1030+point (1327/200) 4096 1031)/2 = (4362947:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1030
  · change cPayment 1031 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1031+point (1327/200) 4096 1032)/2)
    have hp : cPayment 1031 = (82273062874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1031+point (1327/200) 4096 1032)/2 = (4364001:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1031
  · change cPayment 1032 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1032+point (1327/200) 4096 1033)/2)
    have hp : cPayment 1032 = (82282110870:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1032+point (1327/200) 4096 1033)/2 = (873011:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1032
  · change cPayment 1033 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1033+point (1327/200) 4096 1034)/2)
    have hp : cPayment 1033 = (82291085323:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1033+point (1327/200) 4096 1034)/2 = (4366109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1033
  · change cPayment 1034 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1034+point (1327/200) 4096 1035)/2)
    have hp : cPayment 1034 = (82299986346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1034+point (1327/200) 4096 1035)/2 = (4367163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1034
  · change cPayment 1035 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1035+point (1327/200) 4096 1036)/2)
    have hp : cPayment 1035 = (82308814051:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1035+point (1327/200) 4096 1036)/2 = (4368217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1035
  · change cPayment 1036 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1036+point (1327/200) 4096 1037)/2)
    have hp : cPayment 1036 = (82317568550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1036+point (1327/200) 4096 1037)/2 = (4369271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1036
  · change cPayment 1037 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1037+point (1327/200) 4096 1038)/2)
    have hp : cPayment 1037 = (82326249956:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1037+point (1327/200) 4096 1038)/2 = (174813:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1037
  · change cPayment 1038 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1038+point (1327/200) 4096 1039)/2)
    have hp : cPayment 1038 = (82334858381:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1038+point (1327/200) 4096 1039)/2 = (4371379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1038
  · change cPayment 1039 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1039+point (1327/200) 4096 1040)/2)
    have hp : cPayment 1039 = (82343393937:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1039+point (1327/200) 4096 1040)/2 = (4372433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1039
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_064
