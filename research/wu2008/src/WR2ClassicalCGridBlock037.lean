import WR2ClassicalCPayments
import WR2ClassicalCPoints037
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_037 (j : Fin 16) : cPayment (16*37+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*37+j.val)+point (1327/200) 4096 (16*37+j.val+1))/2) := by
  fin_cases j
  · change cPayment 592 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 592+point (1327/200) 4096 593)/2)
    have hp : cPayment 592 = (69269910283:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 592+point (1327/200) 4096 593)/2 = (780259:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_592
  · change cPayment 593 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 593+point (1327/200) 4096 594)/2)
    have hp : cPayment 593 = (69325232479:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 593+point (1327/200) 4096 594)/2 = (3902349:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_593
  · change cPayment 594 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 594+point (1327/200) 4096 595)/2)
    have hp : cPayment 594 = (69380408915:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 594+point (1327/200) 4096 595)/2 = (3903403:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_594
  · change cPayment 595 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 595+point (1327/200) 4096 596)/2)
    have hp : cPayment 595 = (69435439823:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 595+point (1327/200) 4096 596)/2 = (3904457:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_595
  · change cPayment 596 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 596+point (1327/200) 4096 597)/2)
    have hp : cPayment 596 = (69490325435:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 596+point (1327/200) 4096 597)/2 = (3905511:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_596
  · change cPayment 597 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 597+point (1327/200) 4096 598)/2)
    have hp : cPayment 597 = (69545065983:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 597+point (1327/200) 4096 598)/2 = (781313:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_597
  · change cPayment 598 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 598+point (1327/200) 4096 599)/2)
    have hp : cPayment 598 = (69599661698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 598+point (1327/200) 4096 599)/2 = (3907619:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_598
  · change cPayment 599 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 599+point (1327/200) 4096 600)/2)
    have hp : cPayment 599 = (69654112810:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 599+point (1327/200) 4096 600)/2 = (3908673:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_599
  · change cPayment 600 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 600+point (1327/200) 4096 601)/2)
    have hp : cPayment 600 = (69708419550:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 600+point (1327/200) 4096 601)/2 = (3909727:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_600
  · change cPayment 601 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 601+point (1327/200) 4096 602)/2)
    have hp : cPayment 601 = (69762582148:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 601+point (1327/200) 4096 602)/2 = (3910781:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_601
  · change cPayment 602 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 602+point (1327/200) 4096 603)/2)
    have hp : cPayment 602 = (69816600834:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 602+point (1327/200) 4096 603)/2 = (782367:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_602
  · change cPayment 603 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 603+point (1327/200) 4096 604)/2)
    have hp : cPayment 603 = (69870475837:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 603+point (1327/200) 4096 604)/2 = (3912889:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_603
  · change cPayment 604 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 604+point (1327/200) 4096 605)/2)
    have hp : cPayment 604 = (69924207386:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 604+point (1327/200) 4096 605)/2 = (3913943:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_604
  · change cPayment 605 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 605+point (1327/200) 4096 606)/2)
    have hp : cPayment 605 = (69977795710:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 605+point (1327/200) 4096 606)/2 = (3914997:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_605
  · change cPayment 606 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 606+point (1327/200) 4096 607)/2)
    have hp : cPayment 606 = (70031241035:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 606+point (1327/200) 4096 607)/2 = (3916051:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_606
  · change cPayment 607 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 607+point (1327/200) 4096 608)/2)
    have hp : cPayment 607 = (70084543591:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 607+point (1327/200) 4096 608)/2 = (783421:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_607
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_037
