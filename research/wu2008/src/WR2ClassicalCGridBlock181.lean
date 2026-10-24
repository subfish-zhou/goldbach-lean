import WR2ClassicalCPayments
import WR2ClassicalCPoints181
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_181 (j : Fin 16) : cPayment (16*181+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*181+j.val)+point (1327/200) 4096 (16*181+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2896 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2896+point (1327/200) 4096 2897)/2)
    have hp : cPayment 2896 = (40101656527:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2896+point (1327/200) 4096 2897)/2 = (6329711:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2896
  · change cPayment 2897 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2897+point (1327/200) 4096 2898)/2)
    have hp : cPayment 2897 = (40067523578:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2897+point (1327/200) 4096 2898)/2 = (1266153:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2897
  · change cPayment 2898 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2898+point (1327/200) 4096 2899)/2)
    have hp : cPayment 2898 = (40033389460:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2898+point (1327/200) 4096 2899)/2 = (6331819:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2898
  · change cPayment 2899 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2899+point (1327/200) 4096 2900)/2)
    have hp : cPayment 2899 = (39999254182:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2899+point (1327/200) 4096 2900)/2 = (6332873:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2899
  · change cPayment 2900 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2900+point (1327/200) 4096 2901)/2)
    have hp : cPayment 2900 = (39965117751:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2900+point (1327/200) 4096 2901)/2 = (6333927:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2900
  · change cPayment 2901 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2901+point (1327/200) 4096 2902)/2)
    have hp : cPayment 2901 = (39930980177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2901+point (1327/200) 4096 2902)/2 = (6334981:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2901
  · change cPayment 2902 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2902+point (1327/200) 4096 2903)/2)
    have hp : cPayment 2902 = (39896841467:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2902+point (1327/200) 4096 2903)/2 = (1267207:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2902
  · change cPayment 2903 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2903+point (1327/200) 4096 2904)/2)
    have hp : cPayment 2903 = (39862701629:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2903+point (1327/200) 4096 2904)/2 = (6337089:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2903
  · change cPayment 2904 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2904+point (1327/200) 4096 2905)/2)
    have hp : cPayment 2904 = (39828560674:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2904+point (1327/200) 4096 2905)/2 = (6338143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2904
  · change cPayment 2905 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2905+point (1327/200) 4096 2906)/2)
    have hp : cPayment 2905 = (39794418607:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2905+point (1327/200) 4096 2906)/2 = (6339197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2905
  · change cPayment 2906 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2906+point (1327/200) 4096 2907)/2)
    have hp : cPayment 2906 = (39760275439:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2906+point (1327/200) 4096 2907)/2 = (6340251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2906
  · change cPayment 2907 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2907+point (1327/200) 4096 2908)/2)
    have hp : cPayment 2907 = (39726131177:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2907+point (1327/200) 4096 2908)/2 = (1268261:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2907
  · change cPayment 2908 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2908+point (1327/200) 4096 2909)/2)
    have hp : cPayment 2908 = (39691985829:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2908+point (1327/200) 4096 2909)/2 = (6342359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2908
  · change cPayment 2909 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2909+point (1327/200) 4096 2910)/2)
    have hp : cPayment 2909 = (39657839405:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2909+point (1327/200) 4096 2910)/2 = (6343413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2909
  · change cPayment 2910 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2910+point (1327/200) 4096 2911)/2)
    have hp : cPayment 2910 = (39623691911:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2910+point (1327/200) 4096 2911)/2 = (6344467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2910
  · change cPayment 2911 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2911+point (1327/200) 4096 2912)/2)
    have hp : cPayment 2911 = (39589543358:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2911+point (1327/200) 4096 2912)/2 = (6345521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2911
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_181
