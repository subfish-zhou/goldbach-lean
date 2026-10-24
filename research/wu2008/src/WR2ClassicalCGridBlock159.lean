import WR2ClassicalCPayments
import WR2ClassicalCPoints159
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_159 (j : Fin 16) : cPayment (16*159+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*159+j.val)+point (1327/200) 4096 (16*159+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2544 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2544+point (1327/200) 4096 2545)/2)
    have hp : cPayment 2544 = (51974121149:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2544+point (1327/200) 4096 2545)/2 = (5958703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2544
  · change cPayment 2545 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2545+point (1327/200) 4096 2546)/2)
    have hp : cPayment 2545 = (51941015016:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2545+point (1327/200) 4096 2546)/2 = (5959757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2545
  · change cPayment 2546 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2546+point (1327/200) 4096 2547)/2)
    have hp : cPayment 2546 = (51907903935:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2546+point (1327/200) 4096 2547)/2 = (5960811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2546
  · change cPayment 2547 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2547+point (1327/200) 4096 2548)/2)
    have hp : cPayment 2547 = (51874787921:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2547+point (1327/200) 4096 2548)/2 = (1192373:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2547
  · change cPayment 2548 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2548+point (1327/200) 4096 2549)/2)
    have hp : cPayment 2548 = (51841666986:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2548+point (1327/200) 4096 2549)/2 = (5962919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2548
  · change cPayment 2549 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2549+point (1327/200) 4096 2550)/2)
    have hp : cPayment 2549 = (51808541144:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2549+point (1327/200) 4096 2550)/2 = (5963973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2549
  · change cPayment 2550 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2550+point (1327/200) 4096 2551)/2)
    have hp : cPayment 2550 = (51775410408:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2550+point (1327/200) 4096 2551)/2 = (5965027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2550
  · change cPayment 2551 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2551+point (1327/200) 4096 2552)/2)
    have hp : cPayment 2551 = (51742274791:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2551+point (1327/200) 4096 2552)/2 = (5966081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2551
  · change cPayment 2552 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2552+point (1327/200) 4096 2553)/2)
    have hp : cPayment 2552 = (51709134308:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2552+point (1327/200) 4096 2553)/2 = (1193427:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2552
  · change cPayment 2553 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2553+point (1327/200) 4096 2554)/2)
    have hp : cPayment 2553 = (51675988970:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2553+point (1327/200) 4096 2554)/2 = (5968189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2553
  · change cPayment 2554 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2554+point (1327/200) 4096 2555)/2)
    have hp : cPayment 2554 = (51642838792:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2554+point (1327/200) 4096 2555)/2 = (5969243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2554
  · change cPayment 2555 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2555+point (1327/200) 4096 2556)/2)
    have hp : cPayment 2555 = (51609683787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2555+point (1327/200) 4096 2556)/2 = (5970297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2555
  · change cPayment 2556 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2556+point (1327/200) 4096 2557)/2)
    have hp : cPayment 2556 = (51576523968:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2556+point (1327/200) 4096 2557)/2 = (5971351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2556
  · change cPayment 2557 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2557+point (1327/200) 4096 2558)/2)
    have hp : cPayment 2557 = (51543359348:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2557+point (1327/200) 4096 2558)/2 = (1194481:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2557
  · change cPayment 2558 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2558+point (1327/200) 4096 2559)/2)
    have hp : cPayment 2558 = (51510189940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2558+point (1327/200) 4096 2559)/2 = (5973459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2558
  · change cPayment 2559 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2559+point (1327/200) 4096 2560)/2)
    have hp : cPayment 2559 = (51477015759:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2559+point (1327/200) 4096 2560)/2 = (5974513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2559
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_159
