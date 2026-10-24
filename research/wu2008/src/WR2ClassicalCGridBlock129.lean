import WR2ClassicalCPayments
import WR2ClassicalCPoints129
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_129 (j : Fin 16) : cPayment (16*129+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*129+j.val)+point (1327/200) 4096 (16*129+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2064 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2064+point (1327/200) 4096 2065)/2)
    have hp : cPayment 2064 = (66999355347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2064+point (1327/200) 4096 2065)/2 = (5452783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2064
  · change cPayment 2065 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2065+point (1327/200) 4096 2066)/2)
    have hp : cPayment 2065 = (66970564771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2065+point (1327/200) 4096 2066)/2 = (5453837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2065
  · change cPayment 2066 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2066+point (1327/200) 4096 2067)/2)
    have hp : cPayment 2066 = (66941760221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2066+point (1327/200) 4096 2067)/2 = (5454891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2066
  · change cPayment 2067 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2067+point (1327/200) 4096 2068)/2)
    have hp : cPayment 2067 = (66912941725:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2067+point (1327/200) 4096 2068)/2 = (1091189:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2067
  · change cPayment 2068 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2068+point (1327/200) 4096 2069)/2)
    have hp : cPayment 2068 = (66884109307:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2068+point (1327/200) 4096 2069)/2 = (5456999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2068
  · change cPayment 2069 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2069+point (1327/200) 4096 2070)/2)
    have hp : cPayment 2069 = (66855262993:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2069+point (1327/200) 4096 2070)/2 = (5458053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2069
  · change cPayment 2070 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2070+point (1327/200) 4096 2071)/2)
    have hp : cPayment 2070 = (66826402808:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2070+point (1327/200) 4096 2071)/2 = (5459107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2070
  · change cPayment 2071 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2071+point (1327/200) 4096 2072)/2)
    have hp : cPayment 2071 = (66797528778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2071+point (1327/200) 4096 2072)/2 = (5460161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2071
  · change cPayment 2072 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2072+point (1327/200) 4096 2073)/2)
    have hp : cPayment 2072 = (66768640928:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2072+point (1327/200) 4096 2073)/2 = (1092243:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2072
  · change cPayment 2073 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2073+point (1327/200) 4096 2074)/2)
    have hp : cPayment 2073 = (66739739283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2073+point (1327/200) 4096 2074)/2 = (5462269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2073
  · change cPayment 2074 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2074+point (1327/200) 4096 2075)/2)
    have hp : cPayment 2074 = (66710823868:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2074+point (1327/200) 4096 2075)/2 = (5463323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2074
  · change cPayment 2075 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2075+point (1327/200) 4096 2076)/2)
    have hp : cPayment 2075 = (66681894709:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2075+point (1327/200) 4096 2076)/2 = (5464377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2075
  · change cPayment 2076 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2076+point (1327/200) 4096 2077)/2)
    have hp : cPayment 2076 = (66652951831:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2076+point (1327/200) 4096 2077)/2 = (5465431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2076
  · change cPayment 2077 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2077+point (1327/200) 4096 2078)/2)
    have hp : cPayment 2077 = (66623995259:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2077+point (1327/200) 4096 2078)/2 = (1093297:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2077
  · change cPayment 2078 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2078+point (1327/200) 4096 2079)/2)
    have hp : cPayment 2078 = (66595025017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2078+point (1327/200) 4096 2079)/2 = (5467539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2078
  · change cPayment 2079 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2079+point (1327/200) 4096 2080)/2)
    have hp : cPayment 2079 = (66566041132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2079+point (1327/200) 4096 2080)/2 = (5468593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2079
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_129
