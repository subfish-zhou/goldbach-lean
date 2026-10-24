import WR2ClassicalCPayments
import WR2ClassicalCPoints133
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_133 (j : Fin 16) : cPayment (16*133+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*133+j.val)+point (1327/200) 4096 (16*133+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2128 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2128+point (1327/200) 4096 2129)/2)
    have hp : cPayment 2128 = (65129629922:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2128+point (1327/200) 4096 2129)/2 = (5520239:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2128
  · change cPayment 2129 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2129+point (1327/200) 4096 2130)/2)
    have hp : cPayment 2129 = (65099995066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2129+point (1327/200) 4096 2130)/2 = (5521293:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2129
  · change cPayment 2130 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2130+point (1327/200) 4096 2131)/2)
    have hp : cPayment 2130 = (65070347799:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2130+point (1327/200) 4096 2131)/2 = (5522347:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2130
  · change cPayment 2131 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2131+point (1327/200) 4096 2132)/2)
    have hp : cPayment 2131 = (65040688147:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2131+point (1327/200) 4096 2132)/2 = (5523401:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2131
  · change cPayment 2132 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2132+point (1327/200) 4096 2133)/2)
    have hp : cPayment 2132 = (65011016133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2132+point (1327/200) 4096 2133)/2 = (1104891:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2132
  · change cPayment 2133 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2133+point (1327/200) 4096 2134)/2)
    have hp : cPayment 2133 = (64981331779:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2133+point (1327/200) 4096 2134)/2 = (5525509:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2133
  · change cPayment 2134 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2134+point (1327/200) 4096 2135)/2)
    have hp : cPayment 2134 = (64951635108:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2134+point (1327/200) 4096 2135)/2 = (5526563:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2134
  · change cPayment 2135 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2135+point (1327/200) 4096 2136)/2)
    have hp : cPayment 2135 = (64921926145:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2135+point (1327/200) 4096 2136)/2 = (5527617:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2135
  · change cPayment 2136 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2136+point (1327/200) 4096 2137)/2)
    have hp : cPayment 2136 = (64892204913:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2136+point (1327/200) 4096 2137)/2 = (5528671:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2136
  · change cPayment 2137 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2137+point (1327/200) 4096 2138)/2)
    have hp : cPayment 2137 = (64862471434:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2137+point (1327/200) 4096 2138)/2 = (221189:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2137
  · change cPayment 2138 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2138+point (1327/200) 4096 2139)/2)
    have hp : cPayment 2138 = (64832725731:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2138+point (1327/200) 4096 2139)/2 = (5530779:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2138
  · change cPayment 2139 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2139+point (1327/200) 4096 2140)/2)
    have hp : cPayment 2139 = (64802967829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2139+point (1327/200) 4096 2140)/2 = (5531833:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2139
  · change cPayment 2140 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2140+point (1327/200) 4096 2141)/2)
    have hp : cPayment 2140 = (64773197749:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2140+point (1327/200) 4096 2141)/2 = (5532887:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2140
  · change cPayment 2141 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2141+point (1327/200) 4096 2142)/2)
    have hp : cPayment 2141 = (64743415515:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2141+point (1327/200) 4096 2142)/2 = (5533941:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2141
  · change cPayment 2142 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2142+point (1327/200) 4096 2143)/2)
    have hp : cPayment 2142 = (64713621150:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2142+point (1327/200) 4096 2143)/2 = (1106999:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2142
  · change cPayment 2143 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2143+point (1327/200) 4096 2144)/2)
    have hp : cPayment 2143 = (64683814678:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2143+point (1327/200) 4096 2144)/2 = (5536049:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2143
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_133
