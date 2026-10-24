import WR2ClassicalCPayments
import WR2ClassicalCPoints173
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_173 (j : Fin 16) : cPayment (16*173+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*173+j.val)+point (1327/200) 4096 (16*173+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2768 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2768+point (1327/200) 4096 2769)/2)
    have hp : cPayment 2768 = (44457876458:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2768+point (1327/200) 4096 2769)/2 = (6194799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2768
  · change cPayment 2769 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2769+point (1327/200) 4096 2770)/2)
    have hp : cPayment 2769 = (44423966794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2769+point (1327/200) 4096 2770)/2 = (6195853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2769
  · change cPayment 2770 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2770+point (1327/200) 4096 2771)/2)
    have hp : cPayment 2770 = (44390054786:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2770+point (1327/200) 4096 2771)/2 = (6196907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2770
  · change cPayment 2771 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2771+point (1327/200) 4096 2772)/2)
    have hp : cPayment 2771 = (44356140444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2771+point (1327/200) 4096 2772)/2 = (6197961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2771
  · change cPayment 2772 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2772+point (1327/200) 4096 2773)/2)
    have hp : cPayment 2772 = (44322223778:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2772+point (1327/200) 4096 2773)/2 = (1239803:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2772
  · change cPayment 2773 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2773+point (1327/200) 4096 2774)/2)
    have hp : cPayment 2773 = (44288304798:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2773+point (1327/200) 4096 2774)/2 = (6200069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2773
  · change cPayment 2774 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2774+point (1327/200) 4096 2775)/2)
    have hp : cPayment 2774 = (44254383514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2774+point (1327/200) 4096 2775)/2 = (6201123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2774
  · change cPayment 2775 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2775+point (1327/200) 4096 2776)/2)
    have hp : cPayment 2775 = (44220459935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2775+point (1327/200) 4096 2776)/2 = (6202177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2775
  · change cPayment 2776 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2776+point (1327/200) 4096 2777)/2)
    have hp : cPayment 2776 = (44186534073:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2776+point (1327/200) 4096 2777)/2 = (6203231:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2776
  · change cPayment 2777 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2777+point (1327/200) 4096 2778)/2)
    have hp : cPayment 2777 = (44152605936:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2777+point (1327/200) 4096 2778)/2 = (1240857:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2777
  · change cPayment 2778 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2778+point (1327/200) 4096 2779)/2)
    have hp : cPayment 2778 = (44118675534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2778+point (1327/200) 4096 2779)/2 = (6205339:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2778
  · change cPayment 2779 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2779+point (1327/200) 4096 2780)/2)
    have hp : cPayment 2779 = (44084742878:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2779+point (1327/200) 4096 2780)/2 = (6206393:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2779
  · change cPayment 2780 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2780+point (1327/200) 4096 2781)/2)
    have hp : cPayment 2780 = (44050807977:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2780+point (1327/200) 4096 2781)/2 = (6207447:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2780
  · change cPayment 2781 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2781+point (1327/200) 4096 2782)/2)
    have hp : cPayment 2781 = (44016870841:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2781+point (1327/200) 4096 2782)/2 = (6208501:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2781
  · change cPayment 2782 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2782+point (1327/200) 4096 2783)/2)
    have hp : cPayment 2782 = (43982931480:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2782+point (1327/200) 4096 2783)/2 = (1241911:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2782
  · change cPayment 2783 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2783+point (1327/200) 4096 2784)/2)
    have hp : cPayment 2783 = (43948989904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2783+point (1327/200) 4096 2784)/2 = (6210609:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2783
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_173
