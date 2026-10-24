import WR2ClassicalCPayments
import WR2ClassicalCPoints132
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_132 (j : Fin 16) : cPayment (16*132+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*132+j.val)+point (1327/200) 4096 (16*132+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2112 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2112+point (1327/200) 4096 2113)/2)
    have hp : cPayment 2112 = (65602080764:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2112+point (1327/200) 4096 2113)/2 = (220135:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2112
  · change cPayment 2113 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2113+point (1327/200) 4096 2114)/2)
    have hp : cPayment 2113 = (65572647662:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2113+point (1327/200) 4096 2114)/2 = (5504429:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2113
  · change cPayment 2114 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2114+point (1327/200) 4096 2115)/2)
    have hp : cPayment 2114 = (65543201771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2114+point (1327/200) 4096 2115)/2 = (5505483:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2114
  · change cPayment 2115 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2115+point (1327/200) 4096 2116)/2)
    have hp : cPayment 2115 = (65513743117:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2115+point (1327/200) 4096 2116)/2 = (5506537:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2115
  · change cPayment 2116 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2116+point (1327/200) 4096 2117)/2)
    have hp : cPayment 2116 = (65484271723:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2116+point (1327/200) 4096 2117)/2 = (5507591:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2116
  · change cPayment 2117 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2117+point (1327/200) 4096 2118)/2)
    have hp : cPayment 2117 = (65454787613:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2117+point (1327/200) 4096 2118)/2 = (1101729:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2117
  · change cPayment 2118 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2118+point (1327/200) 4096 2119)/2)
    have hp : cPayment 2118 = (65425290811:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2118+point (1327/200) 4096 2119)/2 = (5509699:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2118
  · change cPayment 2119 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2119+point (1327/200) 4096 2120)/2)
    have hp : cPayment 2119 = (65395781340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2119+point (1327/200) 4096 2120)/2 = (5510753:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2119
  · change cPayment 2120 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2120+point (1327/200) 4096 2121)/2)
    have hp : cPayment 2120 = (65366259224:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2120+point (1327/200) 4096 2121)/2 = (5511807:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2120
  · change cPayment 2121 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2121+point (1327/200) 4096 2122)/2)
    have hp : cPayment 2121 = (65336724487:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2121+point (1327/200) 4096 2122)/2 = (5512861:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2121
  · change cPayment 2122 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2122+point (1327/200) 4096 2123)/2)
    have hp : cPayment 2122 = (65307177153:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2122+point (1327/200) 4096 2123)/2 = (1102783:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2122
  · change cPayment 2123 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2123+point (1327/200) 4096 2124)/2)
    have hp : cPayment 2123 = (65277617245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2123+point (1327/200) 4096 2124)/2 = (5514969:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2123
  · change cPayment 2124 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2124+point (1327/200) 4096 2125)/2)
    have hp : cPayment 2124 = (65248044787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2124+point (1327/200) 4096 2125)/2 = (5516023:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2124
  · change cPayment 2125 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2125+point (1327/200) 4096 2126)/2)
    have hp : cPayment 2125 = (65218459802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2125+point (1327/200) 4096 2126)/2 = (5517077:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2125
  · change cPayment 2126 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2126+point (1327/200) 4096 2127)/2)
    have hp : cPayment 2126 = (65188862314:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2126+point (1327/200) 4096 2127)/2 = (5518131:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2126
  · change cPayment 2127 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2127+point (1327/200) 4096 2128)/2)
    have hp : cPayment 2127 = (65159252346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2127+point (1327/200) 4096 2128)/2 = (1103837:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2127
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_132
