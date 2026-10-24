import WR2ClassicalCPayments
import WR2ClassicalCPoints123
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_123 (j : Fin 16) : cPayment (16*123+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*123+j.val)+point (1327/200) 4096 (16*123+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1968 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1968+point (1327/200) 4096 1969)/2)
    have hp : cPayment 1968 = (69694186808:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1968+point (1327/200) 4096 1969)/2 = (5351599:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1968
  · change cPayment 1969 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1969+point (1327/200) 4096 1970)/2)
    have hp : cPayment 1969 = (69666861630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1969+point (1327/200) 4096 1970)/2 = (5352653:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1969
  · change cPayment 1970 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1970+point (1327/200) 4096 1971)/2)
    have hp : cPayment 1970 = (69639519866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1970+point (1327/200) 4096 1971)/2 = (5353707:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1970
  · change cPayment 1971 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1971+point (1327/200) 4096 1972)/2)
    have hp : cPayment 1971 = (69612161545:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1971+point (1327/200) 4096 1972)/2 = (5354761:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1971
  · change cPayment 1972 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1972+point (1327/200) 4096 1973)/2)
    have hp : cPayment 1972 = (69584786696:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1972+point (1327/200) 4096 1973)/2 = (1071163:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1972
  · change cPayment 1973 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1973+point (1327/200) 4096 1974)/2)
    have hp : cPayment 1973 = (69557395347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1973+point (1327/200) 4096 1974)/2 = (5356869:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1973
  · change cPayment 1974 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1974+point (1327/200) 4096 1975)/2)
    have hp : cPayment 1974 = (69529987528:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1974+point (1327/200) 4096 1975)/2 = (5357923:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1974
  · change cPayment 1975 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1975+point (1327/200) 4096 1976)/2)
    have hp : cPayment 1975 = (69502563268:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1975+point (1327/200) 4096 1976)/2 = (5358977:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1975
  · change cPayment 1976 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1976+point (1327/200) 4096 1977)/2)
    have hp : cPayment 1976 = (69475122595:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1976+point (1327/200) 4096 1977)/2 = (5360031:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1976
  · change cPayment 1977 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1977+point (1327/200) 4096 1978)/2)
    have hp : cPayment 1977 = (69447665538:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1977+point (1327/200) 4096 1978)/2 = (1072217:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1977
  · change cPayment 1978 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1978+point (1327/200) 4096 1979)/2)
    have hp : cPayment 1978 = (69420192125:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1978+point (1327/200) 4096 1979)/2 = (5362139:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1978
  · change cPayment 1979 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1979+point (1327/200) 4096 1980)/2)
    have hp : cPayment 1979 = (69392702387:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1979+point (1327/200) 4096 1980)/2 = (5363193:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1979
  · change cPayment 1980 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1980+point (1327/200) 4096 1981)/2)
    have hp : cPayment 1980 = (69365196350:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1980+point (1327/200) 4096 1981)/2 = (5364247:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1980
  · change cPayment 1981 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1981+point (1327/200) 4096 1982)/2)
    have hp : cPayment 1981 = (69337674044:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1981+point (1327/200) 4096 1982)/2 = (5365301:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1981
  · change cPayment 1982 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1982+point (1327/200) 4096 1983)/2)
    have hp : cPayment 1982 = (69310135498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1982+point (1327/200) 4096 1983)/2 = (1073271:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1982
  · change cPayment 1983 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1983+point (1327/200) 4096 1984)/2)
    have hp : cPayment 1983 = (69282580740:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1983+point (1327/200) 4096 1984)/2 = (5367409:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1983
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_123
