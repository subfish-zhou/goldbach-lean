import WR2ClassicalCPayments
import WR2ClassicalCPoints004
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_004 (j : Fin 16) : cPayment (16*4+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*4+j.val)+point (1327/200) 4096 (16*4+j.val+1))/2) := by
  fin_cases j
  · change cPayment 64 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 64+point (1327/200) 4096 65)/2)
    have hp : cPayment 64 = (12280380731:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 64+point (1327/200) 4096 65)/2 = (3344783:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_64
  · change cPayment 65 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 65+point (1327/200) 4096 66)/2)
    have hp : cPayment 65 = (12458696588:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 65+point (1327/200) 4096 66)/2 = (3345837:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_65
  · change cPayment 66 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 66+point (1327/200) 4096 67)/2)
    have hp : cPayment 66 = (12636658244:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 66+point (1327/200) 4096 67)/2 = (3346891:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_66
  · change cPayment 67 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 67+point (1327/200) 4096 68)/2)
    have hp : cPayment 67 = (12814266335:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 67+point (1327/200) 4096 68)/2 = (669589:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_67
  · change cPayment 68 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 68+point (1327/200) 4096 69)/2)
    have hp : cPayment 68 = (12991521492:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 68+point (1327/200) 4096 69)/2 = (3348999:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_68
  · change cPayment 69 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 69+point (1327/200) 4096 70)/2)
    have hp : cPayment 69 = (13168424348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 69+point (1327/200) 4096 70)/2 = (3350053:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_69
  · change cPayment 70 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 70+point (1327/200) 4096 71)/2)
    have hp : cPayment 70 = (13344975534:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 70+point (1327/200) 4096 71)/2 = (3351107:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_70
  · change cPayment 71 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 71+point (1327/200) 4096 72)/2)
    have hp : cPayment 71 = (13521175679:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 71+point (1327/200) 4096 72)/2 = (3352161:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_71
  · change cPayment 72 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 72+point (1327/200) 4096 73)/2)
    have hp : cPayment 72 = (13697025411:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 72+point (1327/200) 4096 73)/2 = (670643:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_72
  · change cPayment 73 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 73+point (1327/200) 4096 74)/2)
    have hp : cPayment 73 = (13872525356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 73+point (1327/200) 4096 74)/2 = (3354269:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_73
  · change cPayment 74 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 74+point (1327/200) 4096 75)/2)
    have hp : cPayment 74 = (14047676141:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 74+point (1327/200) 4096 75)/2 = (3355323:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_74
  · change cPayment 75 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 75+point (1327/200) 4096 76)/2)
    have hp : cPayment 75 = (14222478389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 75+point (1327/200) 4096 76)/2 = (3356377:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_75
  · change cPayment 76 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 76+point (1327/200) 4096 77)/2)
    have hp : cPayment 76 = (14396932724:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 76+point (1327/200) 4096 77)/2 = (3357431:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_76
  · change cPayment 77 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 77+point (1327/200) 4096 78)/2)
    have hp : cPayment 77 = (14571039765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 77+point (1327/200) 4096 78)/2 = (671697:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_77
  · change cPayment 78 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 78+point (1327/200) 4096 79)/2)
    have hp : cPayment 78 = (14744800135:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 78+point (1327/200) 4096 79)/2 = (3359539:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_78
  · change cPayment 79 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 79+point (1327/200) 4096 80)/2)
    have hp : cPayment 79 = (14918214451:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 79+point (1327/200) 4096 80)/2 = (3360593:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_79
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_004
