import WR2ClassicalCPayments
import WR2ClassicalCPoints178
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_178 (j : Fin 16) : cPayment (16*178+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*178+j.val)+point (1327/200) 4096 (16*178+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2848 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2848+point (1327/200) 4096 2849)/2)
    have hp : cPayment 2848 = (41738495540:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2848+point (1327/200) 4096 2849)/2 = (6279119:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2848
  · change cPayment 2849 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2849+point (1327/200) 4096 2850)/2)
    have hp : cPayment 2849 = (41704428823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2849+point (1327/200) 4096 2850)/2 = (6280173:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2849
  · change cPayment 2850 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2850+point (1327/200) 4096 2851)/2)
    have hp : cPayment 2850 = (41670360519:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2850+point (1327/200) 4096 2851)/2 = (6281227:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2850
  · change cPayment 2851 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2851+point (1327/200) 4096 2852)/2)
    have hp : cPayment 2851 = (41636290638:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2851+point (1327/200) 4096 2852)/2 = (6282281:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2851
  · change cPayment 2852 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2852+point (1327/200) 4096 2853)/2)
    have hp : cPayment 2852 = (41602219188:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2852+point (1327/200) 4096 2853)/2 = (1256667:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2852
  · change cPayment 2853 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2853+point (1327/200) 4096 2854)/2)
    have hp : cPayment 2853 = (41568146179:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2853+point (1327/200) 4096 2854)/2 = (6284389:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2853
  · change cPayment 2854 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2854+point (1327/200) 4096 2855)/2)
    have hp : cPayment 2854 = (41534071619:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2854+point (1327/200) 4096 2855)/2 = (6285443:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2854
  · change cPayment 2855 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2855+point (1327/200) 4096 2856)/2)
    have hp : cPayment 2855 = (41499995518:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2855+point (1327/200) 4096 2856)/2 = (6286497:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2855
  · change cPayment 2856 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2856+point (1327/200) 4096 2857)/2)
    have hp : cPayment 2856 = (41465917884:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2856+point (1327/200) 4096 2857)/2 = (6287551:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2856
  · change cPayment 2857 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2857+point (1327/200) 4096 2858)/2)
    have hp : cPayment 2857 = (41431838726:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2857+point (1327/200) 4096 2858)/2 = (1257721:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2857
  · change cPayment 2858 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2858+point (1327/200) 4096 2859)/2)
    have hp : cPayment 2858 = (41397758053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2858+point (1327/200) 4096 2859)/2 = (6289659:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2858
  · change cPayment 2859 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2859+point (1327/200) 4096 2860)/2)
    have hp : cPayment 2859 = (41363675874:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2859+point (1327/200) 4096 2860)/2 = (6290713:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2859
  · change cPayment 2860 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2860+point (1327/200) 4096 2861)/2)
    have hp : cPayment 2860 = (41329592198:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2860+point (1327/200) 4096 2861)/2 = (6291767:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2860
  · change cPayment 2861 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2861+point (1327/200) 4096 2862)/2)
    have hp : cPayment 2861 = (41295507034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2861+point (1327/200) 4096 2862)/2 = (6292821:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2861
  · change cPayment 2862 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2862+point (1327/200) 4096 2863)/2)
    have hp : cPayment 2862 = (41261420390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2862+point (1327/200) 4096 2863)/2 = (251755:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2862
  · change cPayment 2863 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2863+point (1327/200) 4096 2864)/2)
    have hp : cPayment 2863 = (41227332275:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2863+point (1327/200) 4096 2864)/2 = (6294929:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2863
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_178
