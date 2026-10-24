import WR2ClassicalCPayments
import WR2ClassicalCPoints059
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_059 (j : Fin 16) : cPayment (16*59+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*59+j.val)+point (1327/200) 4096 (16*59+j.val+1))/2) := by
  fin_cases j
  · change cPayment 944 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 944+point (1327/200) 4096 945)/2)
    have hp : cPayment 944 = (81191096274:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 944+point (1327/200) 4096 945)/2 = (4272303:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_944
  · change cPayment 945 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 945+point (1327/200) 4096 946)/2)
    have hp : cPayment 945 = (81206994917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 945+point (1327/200) 4096 946)/2 = (4273357:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_945
  · change cPayment 946 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 946+point (1327/200) 4096 947)/2)
    have hp : cPayment 946 = (81222809496:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 946+point (1327/200) 4096 947)/2 = (4274411:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_946
  · change cPayment 947 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 947+point (1327/200) 4096 948)/2)
    have hp : cPayment 947 = (81238540142:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 947+point (1327/200) 4096 948)/2 = (855093:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_947
  · change cPayment 948 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 948+point (1327/200) 4096 949)/2)
    have hp : cPayment 948 = (81254186983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 948+point (1327/200) 4096 949)/2 = (4276519:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_948
  · change cPayment 949 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 949+point (1327/200) 4096 950)/2)
    have hp : cPayment 949 = (81269750149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 949+point (1327/200) 4096 950)/2 = (4277573:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_949
  · change cPayment 950 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 950+point (1327/200) 4096 951)/2)
    have hp : cPayment 950 = (81285229767:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 950+point (1327/200) 4096 951)/2 = (4278627:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_950
  · change cPayment 951 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 951+point (1327/200) 4096 952)/2)
    have hp : cPayment 951 = (81300625968:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 951+point (1327/200) 4096 952)/2 = (4279681:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_951
  · change cPayment 952 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 952+point (1327/200) 4096 953)/2)
    have hp : cPayment 952 = (81315938878:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 952+point (1327/200) 4096 953)/2 = (856147:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_952
  · change cPayment 953 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 953+point (1327/200) 4096 954)/2)
    have hp : cPayment 953 = (81331168626:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 953+point (1327/200) 4096 954)/2 = (4281789:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_953
  · change cPayment 954 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 954+point (1327/200) 4096 955)/2)
    have hp : cPayment 954 = (81346315340:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 954+point (1327/200) 4096 955)/2 = (4282843:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_954
  · change cPayment 955 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 955+point (1327/200) 4096 956)/2)
    have hp : cPayment 955 = (81361379147:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 955+point (1327/200) 4096 956)/2 = (4283897:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_955
  · change cPayment 956 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 956+point (1327/200) 4096 957)/2)
    have hp : cPayment 956 = (81376360176:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 956+point (1327/200) 4096 957)/2 = (4284951:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_956
  · change cPayment 957 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 957+point (1327/200) 4096 958)/2)
    have hp : cPayment 957 = (81391258553:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 957+point (1327/200) 4096 958)/2 = (857201:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_957
  · change cPayment 958 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 958+point (1327/200) 4096 959)/2)
    have hp : cPayment 958 = (81406074406:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 958+point (1327/200) 4096 959)/2 = (4287059:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_958
  · change cPayment 959 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 959+point (1327/200) 4096 960)/2)
    have hp : cPayment 959 = (81420807861:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 959+point (1327/200) 4096 960)/2 = (4288113:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_959
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_059
