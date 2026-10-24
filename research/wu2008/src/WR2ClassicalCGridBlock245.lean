import WR2ClassicalCPayments
import WR2ClassicalCPoints245
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_245 (j : Fin 16) : cPayment (16*245+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*245+j.val)+point (1327/200) 4096 (16*245+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3920 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3920+point (1327/200) 4096 3921)/2)
    have hp : cPayment 3920 = (5635035970:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3920+point (1327/200) 4096 3921)/2 = (7409007:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3920
  · change cPayment 3921 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3921+point (1327/200) 4096 3922)/2)
    have hp : cPayment 3921 = (5602617929:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3921+point (1327/200) 4096 3922)/2 = (7410061:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3921
  · change cPayment 3922 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3922+point (1327/200) 4096 3923)/2)
    have hp : cPayment 3922 = (5570203333:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3922+point (1327/200) 4096 3923)/2 = (1482223:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3922
  · change cPayment 3923 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3923+point (1327/200) 4096 3924)/2)
    have hp : cPayment 3923 = (5537792183:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3923+point (1327/200) 4096 3924)/2 = (7412169:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3923
  · change cPayment 3924 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3924+point (1327/200) 4096 3925)/2)
    have hp : cPayment 3924 = (5505384482:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3924+point (1327/200) 4096 3925)/2 = (7413223:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3924
  · change cPayment 3925 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3925+point (1327/200) 4096 3926)/2)
    have hp : cPayment 3925 = (5472980231:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3925+point (1327/200) 4096 3926)/2 = (7414277:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3925
  · change cPayment 3926 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3926+point (1327/200) 4096 3927)/2)
    have hp : cPayment 3926 = (5440579431:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3926+point (1327/200) 4096 3927)/2 = (7415331:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3926
  · change cPayment 3927 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3927+point (1327/200) 4096 3928)/2)
    have hp : cPayment 3927 = (5408182087:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3927+point (1327/200) 4096 3928)/2 = (1483277:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3927
  · change cPayment 3928 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3928+point (1327/200) 4096 3929)/2)
    have hp : cPayment 3928 = (5375788198:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3928+point (1327/200) 4096 3929)/2 = (7417439:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3928
  · change cPayment 3929 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3929+point (1327/200) 4096 3930)/2)
    have hp : cPayment 3929 = (5343397767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3929+point (1327/200) 4096 3930)/2 = (7418493:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3929
  · change cPayment 3930 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3930+point (1327/200) 4096 3931)/2)
    have hp : cPayment 3930 = (5311010796:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3930+point (1327/200) 4096 3931)/2 = (7419547:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3930
  · change cPayment 3931 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3931+point (1327/200) 4096 3932)/2)
    have hp : cPayment 3931 = (5278627286:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3931+point (1327/200) 4096 3932)/2 = (7420601:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3931
  · change cPayment 3932 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3932+point (1327/200) 4096 3933)/2)
    have hp : cPayment 3932 = (5246247240:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3932+point (1327/200) 4096 3933)/2 = (1484331:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3932
  · change cPayment 3933 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3933+point (1327/200) 4096 3934)/2)
    have hp : cPayment 3933 = (5213870660:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3933+point (1327/200) 4096 3934)/2 = (7422709:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3933
  · change cPayment 3934 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3934+point (1327/200) 4096 3935)/2)
    have hp : cPayment 3934 = (5181497547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3934+point (1327/200) 4096 3935)/2 = (7423763:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3934
  · change cPayment 3935 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3935+point (1327/200) 4096 3936)/2)
    have hp : cPayment 3935 = (5149127903:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3935+point (1327/200) 4096 3936)/2 = (7424817:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3935
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_245
