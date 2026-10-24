import WR2ClassicalCPayments
import WR2ClassicalCPoints131
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_131 (j : Fin 16) : cPayment (16*131+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*131+j.val)+point (1327/200) 4096 (16*131+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2096 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2096+point (1327/200) 4096 2097)/2)
    have hp : cPayment 2096 = (66071251690:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2096+point (1327/200) 4096 2097)/2 = (5486511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2096
  · change cPayment 2097 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2097+point (1327/200) 4096 2098)/2)
    have hp : cPayment 2097 = (66042026462:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2097+point (1327/200) 4096 2098)/2 = (1097513:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2097
  · change cPayment 2098 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2098+point (1327/200) 4096 2099)/2)
    have hp : cPayment 2098 = (66012788060:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2098+point (1327/200) 4096 2099)/2 = (5488619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2098
  · change cPayment 2099 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2099+point (1327/200) 4096 2100)/2)
    have hp : cPayment 2099 = (65983536509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2099+point (1327/200) 4096 2100)/2 = (5489673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2099
  · change cPayment 2100 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2100+point (1327/200) 4096 2101)/2)
    have hp : cPayment 2100 = (65954271832:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2100+point (1327/200) 4096 2101)/2 = (5490727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2100
  · change cPayment 2101 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2101+point (1327/200) 4096 2102)/2)
    have hp : cPayment 2101 = (65924994054:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2101+point (1327/200) 4096 2102)/2 = (5491781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2101
  · change cPayment 2102 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2102+point (1327/200) 4096 2103)/2)
    have hp : cPayment 2102 = (65895703200:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2102+point (1327/200) 4096 2103)/2 = (1098567:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2102
  · change cPayment 2103 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2103+point (1327/200) 4096 2104)/2)
    have hp : cPayment 2103 = (65866399293:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2103+point (1327/200) 4096 2104)/2 = (5493889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2103
  · change cPayment 2104 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2104+point (1327/200) 4096 2105)/2)
    have hp : cPayment 2104 = (65837082358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2104+point (1327/200) 4096 2105)/2 = (5494943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2104
  · change cPayment 2105 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2105+point (1327/200) 4096 2106)/2)
    have hp : cPayment 2105 = (65807752420:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2105+point (1327/200) 4096 2106)/2 = (5495997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2105
  · change cPayment 2106 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2106+point (1327/200) 4096 2107)/2)
    have hp : cPayment 2106 = (65778409501:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2106+point (1327/200) 4096 2107)/2 = (5497051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2106
  · change cPayment 2107 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2107+point (1327/200) 4096 2108)/2)
    have hp : cPayment 2107 = (65749053627:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2107+point (1327/200) 4096 2108)/2 = (1099621:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2107
  · change cPayment 2108 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2108+point (1327/200) 4096 2109)/2)
    have hp : cPayment 2108 = (65719684821:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2108+point (1327/200) 4096 2109)/2 = (5499159:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2108
  · change cPayment 2109 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2109+point (1327/200) 4096 2110)/2)
    have hp : cPayment 2109 = (65690303108:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2109+point (1327/200) 4096 2110)/2 = (5500213:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2109
  · change cPayment 2110 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2110+point (1327/200) 4096 2111)/2)
    have hp : cPayment 2110 = (65660908512:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2110+point (1327/200) 4096 2111)/2 = (5501267:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2110
  · change cPayment 2111 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2111+point (1327/200) 4096 2112)/2)
    have hp : cPayment 2111 = (65631501056:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2111+point (1327/200) 4096 2112)/2 = (5502321:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2111
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_131
