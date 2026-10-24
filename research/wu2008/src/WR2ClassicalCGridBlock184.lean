import WR2ClassicalCPayments
import WR2ClassicalCPoints184
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_184 (j : Fin 16) : cPayment (16*184+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*184+j.val)+point (1327/200) 4096 (16*184+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2944 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2944+point (1327/200) 4096 2945)/2)
    have hp : cPayment 2944 = (38462099652:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2944+point (1327/200) 4096 2945)/2 = (6380303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2944
  · change cPayment 2945 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2945+point (1327/200) 4096 2946)/2)
    have hp : cPayment 2945 = (38427919888:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2945+point (1327/200) 4096 2946)/2 = (6381357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2945
  · change cPayment 2946 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2946+point (1327/200) 4096 2947)/2)
    have hp : cPayment 2946 = (38393739346:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2946+point (1327/200) 4096 2947)/2 = (6382411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2946
  · change cPayment 2947 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2947+point (1327/200) 4096 2948)/2)
    have hp : cPayment 2947 = (38359558034:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2947+point (1327/200) 4096 2948)/2 = (1276693:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2947
  · change cPayment 2948 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2948+point (1327/200) 4096 2949)/2)
    have hp : cPayment 2948 = (38325375960:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2948+point (1327/200) 4096 2949)/2 = (6384519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2948
  · change cPayment 2949 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2949+point (1327/200) 4096 2950)/2)
    have hp : cPayment 2949 = (38291193132:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2949+point (1327/200) 4096 2950)/2 = (6385573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2949
  · change cPayment 2950 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2950+point (1327/200) 4096 2951)/2)
    have hp : cPayment 2950 = (38257009558:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2950+point (1327/200) 4096 2951)/2 = (6386627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2950
  · change cPayment 2951 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2951+point (1327/200) 4096 2952)/2)
    have hp : cPayment 2951 = (38222825246:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2951+point (1327/200) 4096 2952)/2 = (6387681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2951
  · change cPayment 2952 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2952+point (1327/200) 4096 2953)/2)
    have hp : cPayment 2952 = (38188640204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2952+point (1327/200) 4096 2953)/2 = (1277747:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2952
  · change cPayment 2953 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2953+point (1327/200) 4096 2954)/2)
    have hp : cPayment 2953 = (38154454438:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2953+point (1327/200) 4096 2954)/2 = (6389789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2953
  · change cPayment 2954 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2954+point (1327/200) 4096 2955)/2)
    have hp : cPayment 2954 = (38120267958:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2954+point (1327/200) 4096 2955)/2 = (6390843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2954
  · change cPayment 2955 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2955+point (1327/200) 4096 2956)/2)
    have hp : cPayment 2955 = (38086080771:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2955+point (1327/200) 4096 2956)/2 = (6391897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2955
  · change cPayment 2956 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2956+point (1327/200) 4096 2957)/2)
    have hp : cPayment 2956 = (38051892885:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2956+point (1327/200) 4096 2957)/2 = (6392951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2956
  · change cPayment 2957 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2957+point (1327/200) 4096 2958)/2)
    have hp : cPayment 2957 = (38017704307:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2957+point (1327/200) 4096 2958)/2 = (1278801:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2957
  · change cPayment 2958 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2958+point (1327/200) 4096 2959)/2)
    have hp : cPayment 2958 = (37983515046:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2958+point (1327/200) 4096 2959)/2 = (6395059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2958
  · change cPayment 2959 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2959+point (1327/200) 4096 2960)/2)
    have hp : cPayment 2959 = (37949325109:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2959+point (1327/200) 4096 2960)/2 = (6396113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2959
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_184
