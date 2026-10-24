import WR2ClassicalCPayments
import WR2ClassicalCPoints244
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_244 (j : Fin 16) : cPayment (16*244+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*244+j.val)+point (1327/200) 4096 (16*244+j.val+1))/2) := by
  fin_cases j
  · change cPayment 3904 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3904+point (1327/200) 4096 3905)/2)
    have hp : cPayment 3904 = (6154191498:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3904+point (1327/200) 4096 3905)/2 = (7392143:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3904
  · change cPayment 3905 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3905+point (1327/200) 4096 3906)/2)
    have hp : cPayment 3905 = (6121718609:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3905+point (1327/200) 4096 3906)/2 = (7393197:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3905
  · change cPayment 3906 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3906+point (1327/200) 4096 3907)/2)
    have hp : cPayment 3906 = (6089249133:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3906+point (1327/200) 4096 3907)/2 = (7394251:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3906
  · change cPayment 3907 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3907+point (1327/200) 4096 3908)/2)
    have hp : cPayment 3907 = (6056783073:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3907+point (1327/200) 4096 3908)/2 = (1479061:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3907
  · change cPayment 3908 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3908+point (1327/200) 4096 3909)/2)
    have hp : cPayment 3908 = (6024320429:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3908+point (1327/200) 4096 3909)/2 = (7396359:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3908
  · change cPayment 3909 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3909+point (1327/200) 4096 3910)/2)
    have hp : cPayment 3909 = (5991861205:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3909+point (1327/200) 4096 3910)/2 = (7397413:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3909
  · change cPayment 3910 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3910+point (1327/200) 4096 3911)/2)
    have hp : cPayment 3910 = (5959405403:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3910+point (1327/200) 4096 3911)/2 = (7398467:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3910
  · change cPayment 3911 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3911+point (1327/200) 4096 3912)/2)
    have hp : cPayment 3911 = (5926953023:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3911+point (1327/200) 4096 3912)/2 = (7399521:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3911
  · change cPayment 3912 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3912+point (1327/200) 4096 3913)/2)
    have hp : cPayment 3912 = (5894504068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3912+point (1327/200) 4096 3913)/2 = (296023:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3912
  · change cPayment 3913 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3913+point (1327/200) 4096 3914)/2)
    have hp : cPayment 3913 = (5862058541:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3913+point (1327/200) 4096 3914)/2 = (7401629:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3913
  · change cPayment 3914 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3914+point (1327/200) 4096 3915)/2)
    have hp : cPayment 3914 = (5829616443:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3914+point (1327/200) 4096 3915)/2 = (7402683:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3914
  · change cPayment 3915 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3915+point (1327/200) 4096 3916)/2)
    have hp : cPayment 3915 = (5797177775:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3915+point (1327/200) 4096 3916)/2 = (7403737:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3915
  · change cPayment 3916 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3916+point (1327/200) 4096 3917)/2)
    have hp : cPayment 3916 = (5764742541:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3916+point (1327/200) 4096 3917)/2 = (7404791:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3916
  · change cPayment 3917 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3917+point (1327/200) 4096 3918)/2)
    have hp : cPayment 3917 = (5732310741:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3917+point (1327/200) 4096 3918)/2 = (1481169:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3917
  · change cPayment 3918 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3918+point (1327/200) 4096 3919)/2)
    have hp : cPayment 3918 = (5699882378:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3918+point (1327/200) 4096 3919)/2 = (7406899:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3918
  · change cPayment 3919 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 3919+point (1327/200) 4096 3920)/2)
    have hp : cPayment 3919 = (5667457454:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 3919+point (1327/200) 4096 3920)/2 = (7407953:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_3919
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_244
