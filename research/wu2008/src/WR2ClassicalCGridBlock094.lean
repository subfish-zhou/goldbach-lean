import WR2ClassicalCPayments
import WR2ClassicalCPoints094
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_094 (j : Fin 16) : cPayment (16*94+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*94+j.val)+point (1327/200) 4096 (16*94+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1504 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1504+point (1327/200) 4096 1505)/2)
    have hp : cPayment 1504 = (80008049690:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1504+point (1327/200) 4096 1505)/2 = (4862543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1504
  · change cPayment 1505 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1505+point (1327/200) 4096 1506)/2)
    have hp : cPayment 1505 = (79992345904:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1505+point (1327/200) 4096 1506)/2 = (4863597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1505
  · change cPayment 1506 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1506+point (1327/200) 4096 1507)/2)
    have hp : cPayment 1506 = (79976606621:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1506+point (1327/200) 4096 1507)/2 = (4864651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1506
  · change cPayment 1507 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1507+point (1327/200) 4096 1508)/2)
    have hp : cPayment 1507 = (79960831897:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1507+point (1327/200) 4096 1508)/2 = (973141:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1507
  · change cPayment 1508 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1508+point (1327/200) 4096 1509)/2)
    have hp : cPayment 1508 = (79945021787:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1508+point (1327/200) 4096 1509)/2 = (4866759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1508
  · change cPayment 1509 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1509+point (1327/200) 4096 1510)/2)
    have hp : cPayment 1509 = (79929176347:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1509+point (1327/200) 4096 1510)/2 = (4867813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1509
  · change cPayment 1510 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1510+point (1327/200) 4096 1511)/2)
    have hp : cPayment 1510 = (79913295632:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1510+point (1327/200) 4096 1511)/2 = (4868867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1510
  · change cPayment 1511 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1511+point (1327/200) 4096 1512)/2)
    have hp : cPayment 1511 = (79897379698:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1511+point (1327/200) 4096 1512)/2 = (4869921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1511
  · change cPayment 1512 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1512+point (1327/200) 4096 1513)/2)
    have hp : cPayment 1512 = (79881428598:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1512+point (1327/200) 4096 1513)/2 = (194839:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1512
  · change cPayment 1513 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1513+point (1327/200) 4096 1514)/2)
    have hp : cPayment 1513 = (79865442390:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1513+point (1327/200) 4096 1514)/2 = (4872029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1513
  · change cPayment 1514 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1514+point (1327/200) 4096 1515)/2)
    have hp : cPayment 1514 = (79849421126:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1514+point (1327/200) 4096 1515)/2 = (4873083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1514
  · change cPayment 1515 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1515+point (1327/200) 4096 1516)/2)
    have hp : cPayment 1515 = (79833364863:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1515+point (1327/200) 4096 1516)/2 = (4874137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1515
  · change cPayment 1516 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1516+point (1327/200) 4096 1517)/2)
    have hp : cPayment 1516 = (79817273654:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1516+point (1327/200) 4096 1517)/2 = (4875191:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1516
  · change cPayment 1517 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1517+point (1327/200) 4096 1518)/2)
    have hp : cPayment 1517 = (79801147556:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1517+point (1327/200) 4096 1518)/2 = (975249:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1517
  · change cPayment 1518 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1518+point (1327/200) 4096 1519)/2)
    have hp : cPayment 1518 = (79784986622:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1518+point (1327/200) 4096 1519)/2 = (4877299:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1518
  · change cPayment 1519 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1519+point (1327/200) 4096 1520)/2)
    have hp : cPayment 1519 = (79768790906:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1519+point (1327/200) 4096 1520)/2 = (4878353:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1519
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_094
