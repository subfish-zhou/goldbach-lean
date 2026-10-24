import WR2ClassicalCPayments
import WR2ClassicalCPoints167
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_167 (j : Fin 16) : cPayment (16*167+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*167+j.val)+point (1327/200) 4096 (16*167+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2672 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2672+point (1327/200) 4096 2673)/2)
    have hp : cPayment 2672 = (47700722431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2672+point (1327/200) 4096 2673)/2 = (1218723:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2672
  · change cPayment 2673 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2673+point (1327/200) 4096 2674)/2)
    have hp : cPayment 2673 = (47667086311:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2673+point (1327/200) 4096 2674)/2 = (6094669:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2673
  · change cPayment 2674 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2674+point (1327/200) 4096 2675)/2)
    have hp : cPayment 2674 = (47633446826:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2674+point (1327/200) 4096 2675)/2 = (6095723:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2674
  · change cPayment 2675 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2675+point (1327/200) 4096 2676)/2)
    have hp : cPayment 2675 = (47599803985:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2675+point (1327/200) 4096 2676)/2 = (6096777:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2675
  · change cPayment 2676 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2676+point (1327/200) 4096 2677)/2)
    have hp : cPayment 2676 = (47566157802:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2676+point (1327/200) 4096 2677)/2 = (6097831:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2676
  · change cPayment 2677 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2677+point (1327/200) 4096 2678)/2)
    have hp : cPayment 2677 = (47532508286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2677+point (1327/200) 4096 2678)/2 = (1219777:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2677
  · change cPayment 2678 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2678+point (1327/200) 4096 2679)/2)
    have hp : cPayment 2678 = (47498855450:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2678+point (1327/200) 4096 2679)/2 = (6099939:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2678
  · change cPayment 2679 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2679+point (1327/200) 4096 2680)/2)
    have hp : cPayment 2679 = (47465199304:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2679+point (1327/200) 4096 2680)/2 = (6100993:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2679
  · change cPayment 2680 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2680+point (1327/200) 4096 2681)/2)
    have hp : cPayment 2680 = (47431539860:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2680+point (1327/200) 4096 2681)/2 = (6102047:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2680
  · change cPayment 2681 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2681+point (1327/200) 4096 2682)/2)
    have hp : cPayment 2681 = (47397877129:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2681+point (1327/200) 4096 2682)/2 = (6103101:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2681
  · change cPayment 2682 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2682+point (1327/200) 4096 2683)/2)
    have hp : cPayment 2682 = (47364211122:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2682+point (1327/200) 4096 2683)/2 = (1220831:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2682
  · change cPayment 2683 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2683+point (1327/200) 4096 2684)/2)
    have hp : cPayment 2683 = (47330541851:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2683+point (1327/200) 4096 2684)/2 = (6105209:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2683
  · change cPayment 2684 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2684+point (1327/200) 4096 2685)/2)
    have hp : cPayment 2684 = (47296869327:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2684+point (1327/200) 4096 2685)/2 = (6106263:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2684
  · change cPayment 2685 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2685+point (1327/200) 4096 2686)/2)
    have hp : cPayment 2685 = (47263193560:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2685+point (1327/200) 4096 2686)/2 = (6107317:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2685
  · change cPayment 2686 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2686+point (1327/200) 4096 2687)/2)
    have hp : cPayment 2686 = (47229514563:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2686+point (1327/200) 4096 2687)/2 = (6108371:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2686
  · change cPayment 2687 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2687+point (1327/200) 4096 2688)/2)
    have hp : cPayment 2687 = (47195832346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2687+point (1327/200) 4096 2688)/2 = (244377:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2687
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_167
