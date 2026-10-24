import WR2ClassicalCPayments
import WR2ClassicalCPoints127
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_127 (j : Fin 16) : cPayment (16*127+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*127+j.val)+point (1327/200) 4096 (16*127+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2032 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2032+point (1327/200) 4096 2033)/2)
    have hp : cPayment 2032 = (67913122090:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2032+point (1327/200) 4096 2033)/2 = (1083811:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2032
  · change cPayment 2033 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2033+point (1327/200) 4096 2034)/2)
    have hp : cPayment 2033 = (67884792291:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2033+point (1327/200) 4096 2034)/2 = (5420109:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2033
  · change cPayment 2034 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2034+point (1327/200) 4096 2035)/2)
    have hp : cPayment 2034 = (67856447686:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2034+point (1327/200) 4096 2035)/2 = (5421163:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2034
  · change cPayment 2035 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2035+point (1327/200) 4096 2036)/2)
    have hp : cPayment 2035 = (67828088301:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2035+point (1327/200) 4096 2036)/2 = (5422217:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2035
  · change cPayment 2036 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2036+point (1327/200) 4096 2037)/2)
    have hp : cPayment 2036 = (67799714164:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2036+point (1327/200) 4096 2037)/2 = (5423271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2036
  · change cPayment 2037 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2037+point (1327/200) 4096 2038)/2)
    have hp : cPayment 2037 = (67771325300:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2037+point (1327/200) 4096 2038)/2 = (216973:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2037
  · change cPayment 2038 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2038+point (1327/200) 4096 2039)/2)
    have hp : cPayment 2038 = (67742921736:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2038+point (1327/200) 4096 2039)/2 = (5425379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2038
  · change cPayment 2039 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2039+point (1327/200) 4096 2040)/2)
    have hp : cPayment 2039 = (67714503499:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2039+point (1327/200) 4096 2040)/2 = (5426433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2039
  · change cPayment 2040 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2040+point (1327/200) 4096 2041)/2)
    have hp : cPayment 2040 = (67686070614:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2040+point (1327/200) 4096 2041)/2 = (5427487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2040
  · change cPayment 2041 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2041+point (1327/200) 4096 2042)/2)
    have hp : cPayment 2041 = (67657623109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2041+point (1327/200) 4096 2042)/2 = (5428541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2041
  · change cPayment 2042 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2042+point (1327/200) 4096 2043)/2)
    have hp : cPayment 2042 = (67629161010:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2042+point (1327/200) 4096 2043)/2 = (1085919:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2042
  · change cPayment 2043 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2043+point (1327/200) 4096 2044)/2)
    have hp : cPayment 2043 = (67600684342:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2043+point (1327/200) 4096 2044)/2 = (5430649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2043
  · change cPayment 2044 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2044+point (1327/200) 4096 2045)/2)
    have hp : cPayment 2044 = (67572193133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2044+point (1327/200) 4096 2045)/2 = (5431703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2044
  · change cPayment 2045 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2045+point (1327/200) 4096 2046)/2)
    have hp : cPayment 2045 = (67543687409:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2045+point (1327/200) 4096 2046)/2 = (5432757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2045
  · change cPayment 2046 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2046+point (1327/200) 4096 2047)/2)
    have hp : cPayment 2046 = (67515167195:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2046+point (1327/200) 4096 2047)/2 = (5433811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2046
  · change cPayment 2047 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2047+point (1327/200) 4096 2048)/2)
    have hp : cPayment 2047 = (67486632518:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2047+point (1327/200) 4096 2048)/2 = (1086973:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2047
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_127
