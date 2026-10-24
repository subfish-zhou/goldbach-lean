import WR2ClassicalCPayments
import WR2ClassicalCPoints053
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_053 (j : Fin 16) : cPayment (16*53+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*53+j.val)+point (1327/200) 4096 (16*53+j.val+1))/2) := by
  fin_cases j
  · change cPayment 848 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 848+point (1327/200) 4096 849)/2)
    have hp : cPayment 848 = (79252950399:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 848+point (1327/200) 4096 849)/2 = (4171119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_848
  · change cPayment 849 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 849+point (1327/200) 4096 850)/2)
    have hp : cPayment 849 = (79277554163:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 849+point (1327/200) 4096 850)/2 = (4172173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_849
  · change cPayment 850 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 850+point (1327/200) 4096 851)/2)
    have hp : cPayment 850 = (79302060427:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 850+point (1327/200) 4096 851)/2 = (4173227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_850
  · change cPayment 851 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 851+point (1327/200) 4096 852)/2)
    have hp : cPayment 851 = (79326469342:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 851+point (1327/200) 4096 852)/2 = (4174281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_851
  · change cPayment 852 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 852+point (1327/200) 4096 853)/2)
    have hp : cPayment 852 = (79350781059:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 852+point (1327/200) 4096 853)/2 = (835067:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_852
  · change cPayment 853 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 853+point (1327/200) 4096 854)/2)
    have hp : cPayment 853 = (79374995727:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 853+point (1327/200) 4096 854)/2 = (4176389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_853
  · change cPayment 854 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 854+point (1327/200) 4096 855)/2)
    have hp : cPayment 854 = (79399113498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 854+point (1327/200) 4096 855)/2 = (4177443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_854
  · change cPayment 855 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 855+point (1327/200) 4096 856)/2)
    have hp : cPayment 855 = (79423134521:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 855+point (1327/200) 4096 856)/2 = (4178497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_855
  · change cPayment 856 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 856+point (1327/200) 4096 857)/2)
    have hp : cPayment 856 = (79447058946:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 856+point (1327/200) 4096 857)/2 = (4179551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_856
  · change cPayment 857 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 857+point (1327/200) 4096 858)/2)
    have hp : cPayment 857 = (79470886923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 857+point (1327/200) 4096 858)/2 = (836121:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_857
  · change cPayment 858 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 858+point (1327/200) 4096 859)/2)
    have hp : cPayment 858 = (79494618601:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 858+point (1327/200) 4096 859)/2 = (4181659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_858
  · change cPayment 859 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 859+point (1327/200) 4096 860)/2)
    have hp : cPayment 859 = (79518254129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 859+point (1327/200) 4096 860)/2 = (4182713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_859
  · change cPayment 860 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 860+point (1327/200) 4096 861)/2)
    have hp : cPayment 860 = (79541793655:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 860+point (1327/200) 4096 861)/2 = (4183767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_860
  · change cPayment 861 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 861+point (1327/200) 4096 862)/2)
    have hp : cPayment 861 = (79565237329:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 861+point (1327/200) 4096 862)/2 = (4184821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_861
  · change cPayment 862 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 862+point (1327/200) 4096 863)/2)
    have hp : cPayment 862 = (79588585299:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 862+point (1327/200) 4096 863)/2 = (167435:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_862
  · change cPayment 863 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 863+point (1327/200) 4096 864)/2)
    have hp : cPayment 863 = (79611837712:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 863+point (1327/200) 4096 864)/2 = (4186929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_863
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_053
