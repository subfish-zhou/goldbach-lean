import WR2ClassicalCPayments
import WR2ClassicalCPoints130
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_130 (j : Fin 16) : cPayment (16*130+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*130+j.val)+point (1327/200) 4096 (16*130+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2080 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2080+point (1327/200) 4096 2081)/2)
    have hp : cPayment 2080 = (66537043628:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2080+point (1327/200) 4096 2081)/2 = (5469647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2080
  · change cPayment 2081 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2081+point (1327/200) 4096 2082)/2)
    have hp : cPayment 2081 = (66508032530:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2081+point (1327/200) 4096 2082)/2 = (5470701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2081
  · change cPayment 2082 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2082+point (1327/200) 4096 2083)/2)
    have hp : cPayment 2082 = (66479007863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2082+point (1327/200) 4096 2083)/2 = (1094351:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2082
  · change cPayment 2083 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2083+point (1327/200) 4096 2084)/2)
    have hp : cPayment 2083 = (66449969652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2083+point (1327/200) 4096 2084)/2 = (5472809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2083
  · change cPayment 2084 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2084+point (1327/200) 4096 2085)/2)
    have hp : cPayment 2084 = (66420917922:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2084+point (1327/200) 4096 2085)/2 = (5473863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2084
  · change cPayment 2085 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2085+point (1327/200) 4096 2086)/2)
    have hp : cPayment 2085 = (66391852698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2085+point (1327/200) 4096 2086)/2 = (5474917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2085
  · change cPayment 2086 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2086+point (1327/200) 4096 2087)/2)
    have hp : cPayment 2086 = (66362774004:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2086+point (1327/200) 4096 2087)/2 = (5475971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2086
  · change cPayment 2087 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2087+point (1327/200) 4096 2088)/2)
    have hp : cPayment 2087 = (66333681866:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2087+point (1327/200) 4096 2088)/2 = (219081:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2087
  · change cPayment 2088 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2088+point (1327/200) 4096 2089)/2)
    have hp : cPayment 2088 = (66304576308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2088+point (1327/200) 4096 2089)/2 = (5478079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2088
  · change cPayment 2089 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2089+point (1327/200) 4096 2090)/2)
    have hp : cPayment 2089 = (66275457355:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2089+point (1327/200) 4096 2090)/2 = (5479133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2089
  · change cPayment 2090 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2090+point (1327/200) 4096 2091)/2)
    have hp : cPayment 2090 = (66246325031:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2090+point (1327/200) 4096 2091)/2 = (5480187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2090
  · change cPayment 2091 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2091+point (1327/200) 4096 2092)/2)
    have hp : cPayment 2091 = (66217179362:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2091+point (1327/200) 4096 2092)/2 = (5481241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2091
  · change cPayment 2092 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2092+point (1327/200) 4096 2093)/2)
    have hp : cPayment 2092 = (66188020371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2092+point (1327/200) 4096 2093)/2 = (1096459:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2092
  · change cPayment 2093 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2093+point (1327/200) 4096 2094)/2)
    have hp : cPayment 2093 = (66158848084:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2093+point (1327/200) 4096 2094)/2 = (5483349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2093
  · change cPayment 2094 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2094+point (1327/200) 4096 2095)/2)
    have hp : cPayment 2094 = (66129662525:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2094+point (1327/200) 4096 2095)/2 = (5484403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2094
  · change cPayment 2095 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2095+point (1327/200) 4096 2096)/2)
    have hp : cPayment 2095 = (66100463719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2095+point (1327/200) 4096 2096)/2 = (5485457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2095
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_130
