import WR2ClassicalCPayments
import WR2ClassicalCPoints034
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_034 (j : Fin 16) : cPayment (16*34+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*34+j.val)+point (1327/200) 4096 (16*34+j.val+1))/2) := by
  fin_cases j
  · change cPayment 544 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 544+point (1327/200) 4096 545)/2)
    have hp : cPayment 544 = (66438371085:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 544+point (1327/200) 4096 545)/2 = (3850703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_544
  · change cPayment 545 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 545+point (1327/200) 4096 546)/2)
    have hp : cPayment 545 = (66500971294:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 545+point (1327/200) 4096 546)/2 = (3851757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_545
  · change cPayment 546 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 546+point (1327/200) 4096 547)/2)
    have hp : cPayment 546 = (66563414092:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 546+point (1327/200) 4096 547)/2 = (3852811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_546
  · change cPayment 547 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 547+point (1327/200) 4096 548)/2)
    have hp : cPayment 547 = (66625699732:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 547+point (1327/200) 4096 548)/2 = (770773:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_547
  · change cPayment 548 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 548+point (1327/200) 4096 549)/2)
    have hp : cPayment 548 = (66687828466:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 548+point (1327/200) 4096 549)/2 = (3854919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_548
  · change cPayment 549 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 549+point (1327/200) 4096 550)/2)
    have hp : cPayment 549 = (66749800547:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 549+point (1327/200) 4096 550)/2 = (3855973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_549
  · change cPayment 550 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 550+point (1327/200) 4096 551)/2)
    have hp : cPayment 550 = (66811616227:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 550+point (1327/200) 4096 551)/2 = (3857027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_550
  · change cPayment 551 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 551+point (1327/200) 4096 552)/2)
    have hp : cPayment 551 = (66873275755:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 551+point (1327/200) 4096 552)/2 = (3858081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_551
  · change cPayment 552 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 552+point (1327/200) 4096 553)/2)
    have hp : cPayment 552 = (66934779383:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 552+point (1327/200) 4096 553)/2 = (771827:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_552
  · change cPayment 553 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 553+point (1327/200) 4096 554)/2)
    have hp : cPayment 553 = (66996127361:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 553+point (1327/200) 4096 554)/2 = (3860189:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_553
  · change cPayment 554 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 554+point (1327/200) 4096 555)/2)
    have hp : cPayment 554 = (67057319939:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 554+point (1327/200) 4096 555)/2 = (3861243:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_554
  · change cPayment 555 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 555+point (1327/200) 4096 556)/2)
    have hp : cPayment 555 = (67118357366:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 555+point (1327/200) 4096 556)/2 = (3862297:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_555
  · change cPayment 556 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 556+point (1327/200) 4096 557)/2)
    have hp : cPayment 556 = (67179239891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 556+point (1327/200) 4096 557)/2 = (3863351:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_556
  · change cPayment 557 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 557+point (1327/200) 4096 558)/2)
    have hp : cPayment 557 = (67239967763:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 557+point (1327/200) 4096 558)/2 = (772881:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_557
  · change cPayment 558 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 558+point (1327/200) 4096 559)/2)
    have hp : cPayment 558 = (67300541229:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 558+point (1327/200) 4096 559)/2 = (3865459:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_558
  · change cPayment 559 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 559+point (1327/200) 4096 560)/2)
    have hp : cPayment 559 = (67360960537:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 559+point (1327/200) 4096 560)/2 = (3866513:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_559
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_034
