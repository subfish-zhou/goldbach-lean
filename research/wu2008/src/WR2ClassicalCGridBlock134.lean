import WR2ClassicalCPayments
import WR2ClassicalCPoints134
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_134 (j : Fin 16) : cPayment (16*134+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*134+j.val)+point (1327/200) 4096 (16*134+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2144 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2144+point (1327/200) 4096 2145)/2)
    have hp : cPayment 2144 = (64653996120:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2144+point (1327/200) 4096 2145)/2 = (5537103:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2144
  · change cPayment 2145 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2145+point (1327/200) 4096 2146)/2)
    have hp : cPayment 2145 = (64624165500:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2145+point (1327/200) 4096 2146)/2 = (5538157:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2145
  · change cPayment 2146 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2146+point (1327/200) 4096 2147)/2)
    have hp : cPayment 2146 = (64594322841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2146+point (1327/200) 4096 2147)/2 = (5539211:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2146
  · change cPayment 2147 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2147+point (1327/200) 4096 2148)/2)
    have hp : cPayment 2147 = (64564468165:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2147+point (1327/200) 4096 2148)/2 = (1108053:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2147
  · change cPayment 2148 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2148+point (1327/200) 4096 2149)/2)
    have hp : cPayment 2148 = (64534601496:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2148+point (1327/200) 4096 2149)/2 = (5541319:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2148
  · change cPayment 2149 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2149+point (1327/200) 4096 2150)/2)
    have hp : cPayment 2149 = (64504722857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2149+point (1327/200) 4096 2150)/2 = (5542373:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2149
  · change cPayment 2150 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2150+point (1327/200) 4096 2151)/2)
    have hp : cPayment 2150 = (64474832269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2150+point (1327/200) 4096 2151)/2 = (5543427:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2150
  · change cPayment 2151 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2151+point (1327/200) 4096 2152)/2)
    have hp : cPayment 2151 = (64444929756:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2151+point (1327/200) 4096 2152)/2 = (5544481:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2151
  · change cPayment 2152 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2152+point (1327/200) 4096 2153)/2)
    have hp : cPayment 2152 = (64415015341:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2152+point (1327/200) 4096 2153)/2 = (1109107:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2152
  · change cPayment 2153 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2153+point (1327/200) 4096 2154)/2)
    have hp : cPayment 2153 = (64385089046:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2153+point (1327/200) 4096 2154)/2 = (5546589:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2153
  · change cPayment 2154 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2154+point (1327/200) 4096 2155)/2)
    have hp : cPayment 2154 = (64355150894:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2154+point (1327/200) 4096 2155)/2 = (5547643:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2154
  · change cPayment 2155 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2155+point (1327/200) 4096 2156)/2)
    have hp : cPayment 2155 = (64325200908:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2155+point (1327/200) 4096 2156)/2 = (5548697:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2155
  · change cPayment 2156 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2156+point (1327/200) 4096 2157)/2)
    have hp : cPayment 2156 = (64295239109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2156+point (1327/200) 4096 2157)/2 = (5549751:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2156
  · change cPayment 2157 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2157+point (1327/200) 4096 2158)/2)
    have hp : cPayment 2157 = (64265265521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2157+point (1327/200) 4096 2158)/2 = (1110161:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2157
  · change cPayment 2158 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2158+point (1327/200) 4096 2159)/2)
    have hp : cPayment 2158 = (64235280167:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2158+point (1327/200) 4096 2159)/2 = (5551859:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2158
  · change cPayment 2159 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2159+point (1327/200) 4096 2160)/2)
    have hp : cPayment 2159 = (64205283068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2159+point (1327/200) 4096 2160)/2 = (5552913:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2159
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_134
