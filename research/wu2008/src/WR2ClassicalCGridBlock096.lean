import WR2ClassicalCPayments
import WR2ClassicalCPoints096
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_096 (j : Fin 16) : cPayment (16*96+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*96+j.val)+point (1327/200) 4096 (16*96+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1536 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1536+point (1327/200) 4096 1537)/2)
    have hp : cPayment 1536 = (79488194741:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1536+point (1327/200) 4096 1537)/2 = (4896271:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1536
  · change cPayment 1537 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1537+point (1327/200) 4096 1538)/2)
    have hp : cPayment 1537 = (79471382209:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1537+point (1327/200) 4096 1538)/2 = (195893:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1537
  · change cPayment 1538 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1538+point (1327/200) 4096 1539)/2)
    have hp : cPayment 1538 = (79454535917:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1538+point (1327/200) 4096 1539)/2 = (4898379:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1538
  · change cPayment 1539 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1539+point (1327/200) 4096 1540)/2)
    have hp : cPayment 1539 = (79437655919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1539+point (1327/200) 4096 1540)/2 = (4899433:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1539
  · change cPayment 1540 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1540+point (1327/200) 4096 1541)/2)
    have hp : cPayment 1540 = (79420742269:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1540+point (1327/200) 4096 1541)/2 = (4900487:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1540
  · change cPayment 1541 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1541+point (1327/200) 4096 1542)/2)
    have hp : cPayment 1541 = (79403795017:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1541+point (1327/200) 4096 1542)/2 = (4901541:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1541
  · change cPayment 1542 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1542+point (1327/200) 4096 1543)/2)
    have hp : cPayment 1542 = (79386814219:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1542+point (1327/200) 4096 1543)/2 = (980519:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1542
  · change cPayment 1543 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1543+point (1327/200) 4096 1544)/2)
    have hp : cPayment 1543 = (79369799926:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1543+point (1327/200) 4096 1544)/2 = (4903649:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1543
  · change cPayment 1544 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1544+point (1327/200) 4096 1545)/2)
    have hp : cPayment 1544 = (79352752190:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1544+point (1327/200) 4096 1545)/2 = (4904703:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1544
  · change cPayment 1545 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1545+point (1327/200) 4096 1546)/2)
    have hp : cPayment 1545 = (79335671066:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1545+point (1327/200) 4096 1546)/2 = (4905757:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1545
  · change cPayment 1546 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1546+point (1327/200) 4096 1547)/2)
    have hp : cPayment 1546 = (79318556604:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1546+point (1327/200) 4096 1547)/2 = (4906811:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1546
  · change cPayment 1547 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1547+point (1327/200) 4096 1548)/2)
    have hp : cPayment 1547 = (79301408857:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1547+point (1327/200) 4096 1548)/2 = (981573:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1547
  · change cPayment 1548 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1548+point (1327/200) 4096 1549)/2)
    have hp : cPayment 1548 = (79284227878:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1548+point (1327/200) 4096 1549)/2 = (4908919:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1548
  · change cPayment 1549 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1549+point (1327/200) 4096 1550)/2)
    have hp : cPayment 1549 = (79267013719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1549+point (1327/200) 4096 1550)/2 = (4909973:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1549
  · change cPayment 1550 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1550+point (1327/200) 4096 1551)/2)
    have hp : cPayment 1550 = (79249766433:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1550+point (1327/200) 4096 1551)/2 = (4911027:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1550
  · change cPayment 1551 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1551+point (1327/200) 4096 1552)/2)
    have hp : cPayment 1551 = (79232486070:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1551+point (1327/200) 4096 1552)/2 = (4912081:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1551
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_096
