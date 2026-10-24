import WR2ClassicalCPayments
import WR2ClassicalCPoints005
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_005 (j : Fin 16) : cPayment (16*5+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*5+j.val)+point (1327/200) 4096 (16*5+j.val+1))/2) := by
  fin_cases j
  · change cPayment 80 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 80+point (1327/200) 4096 81)/2)
    have hp : cPayment 80 = (15091283332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 80+point (1327/200) 4096 81)/2 = (3361647:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_80
  · change cPayment 81 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 81+point (1327/200) 4096 82)/2)
    have hp : cPayment 81 = (15264007394:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 81+point (1327/200) 4096 82)/2 = (3362701:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_81
  · change cPayment 82 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 82+point (1327/200) 4096 83)/2)
    have hp : cPayment 82 = (15436387251:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 82+point (1327/200) 4096 83)/2 = (672751:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_82
  · change cPayment 83 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 83+point (1327/200) 4096 84)/2)
    have hp : cPayment 83 = (15608423518:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 83+point (1327/200) 4096 84)/2 = (3364809:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_83
  · change cPayment 84 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 84+point (1327/200) 4096 85)/2)
    have hp : cPayment 84 = (15780116806:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 84+point (1327/200) 4096 85)/2 = (3365863:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_84
  · change cPayment 85 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 85+point (1327/200) 4096 86)/2)
    have hp : cPayment 85 = (15951467729:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 85+point (1327/200) 4096 86)/2 = (3366917:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_85
  · change cPayment 86 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 86+point (1327/200) 4096 87)/2)
    have hp : cPayment 86 = (16122476894:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 86+point (1327/200) 4096 87)/2 = (3367971:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_86
  · change cPayment 87 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 87+point (1327/200) 4096 88)/2)
    have hp : cPayment 87 = (16293144911:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 87+point (1327/200) 4096 88)/2 = (134761:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_87
  · change cPayment 88 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 88+point (1327/200) 4096 89)/2)
    have hp : cPayment 88 = (16463472388:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 88+point (1327/200) 4096 89)/2 = (3370079:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_88
  · change cPayment 89 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 89+point (1327/200) 4096 90)/2)
    have hp : cPayment 89 = (16633459930:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 89+point (1327/200) 4096 90)/2 = (3371133:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_89
  · change cPayment 90 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 90+point (1327/200) 4096 91)/2)
    have hp : cPayment 90 = (16803108143:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 90+point (1327/200) 4096 91)/2 = (3372187:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_90
  · change cPayment 91 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 91+point (1327/200) 4096 92)/2)
    have hp : cPayment 91 = (16972417630:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 91+point (1327/200) 4096 92)/2 = (3373241:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_91
  · change cPayment 92 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 92+point (1327/200) 4096 93)/2)
    have hp : cPayment 92 = (17141388994:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 92+point (1327/200) 4096 93)/2 = (674859:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_92
  · change cPayment 93 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 93+point (1327/200) 4096 94)/2)
    have hp : cPayment 93 = (17310022835:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 93+point (1327/200) 4096 94)/2 = (3375349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_93
  · change cPayment 94 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 94+point (1327/200) 4096 95)/2)
    have hp : cPayment 94 = (17478319754:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 94+point (1327/200) 4096 95)/2 = (3376403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_94
  · change cPayment 95 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 95+point (1327/200) 4096 96)/2)
    have hp : cPayment 95 = (17646280349:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 95+point (1327/200) 4096 96)/2 = (3377457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_95
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_005
