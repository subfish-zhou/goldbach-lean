import WR2ClassicalCPayments
import WR2ClassicalCPoints108
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_108 (j : Fin 16) : cPayment (16*108+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*108+j.val)+point (1327/200) 4096 (16*108+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1728 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1728+point (1327/200) 4096 1729)/2)
    have hp : cPayment 1728 = (75698821805:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1728+point (1327/200) 4096 1729)/2 = (5098639:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1728
  · change cPayment 1729 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1729+point (1327/200) 4096 1730)/2)
    have hp : cPayment 1729 = (75676417703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1729+point (1327/200) 4096 1730)/2 = (5099693:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1729
  · change cPayment 1730 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1730+point (1327/200) 4096 1731)/2)
    have hp : cPayment 1730 = (75653988758:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1730+point (1327/200) 4096 1731)/2 = (5100747:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1730
  · change cPayment 1731 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1731+point (1327/200) 4096 1732)/2)
    have hp : cPayment 1731 = (75631535009:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1731+point (1327/200) 4096 1732)/2 = (5101801:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1731
  · change cPayment 1732 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1732+point (1327/200) 4096 1733)/2)
    have hp : cPayment 1732 = (75609056499:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1732+point (1327/200) 4096 1733)/2 = (1020571:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1732
  · change cPayment 1733 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1733+point (1327/200) 4096 1734)/2)
    have hp : cPayment 1733 = (75586553266:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1733+point (1327/200) 4096 1734)/2 = (5103909:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1733
  · change cPayment 1734 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1734+point (1327/200) 4096 1735)/2)
    have hp : cPayment 1734 = (75564025352:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1734+point (1327/200) 4096 1735)/2 = (5104963:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1734
  · change cPayment 1735 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1735+point (1327/200) 4096 1736)/2)
    have hp : cPayment 1735 = (75541472796:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1735+point (1327/200) 4096 1736)/2 = (5106017:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1735
  · change cPayment 1736 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1736+point (1327/200) 4096 1737)/2)
    have hp : cPayment 1736 = (75518895638:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1736+point (1327/200) 4096 1737)/2 = (5107071:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1736
  · change cPayment 1737 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1737+point (1327/200) 4096 1738)/2)
    have hp : cPayment 1737 = (75496293919:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1737+point (1327/200) 4096 1738)/2 = (204325:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1737
  · change cPayment 1738 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1738+point (1327/200) 4096 1739)/2)
    have hp : cPayment 1738 = (75473667679:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1738+point (1327/200) 4096 1739)/2 = (5109179:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1738
  · change cPayment 1739 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1739+point (1327/200) 4096 1740)/2)
    have hp : cPayment 1739 = (75451016957:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1739+point (1327/200) 4096 1740)/2 = (5110233:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1739
  · change cPayment 1740 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1740+point (1327/200) 4096 1741)/2)
    have hp : cPayment 1740 = (75428341794:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1740+point (1327/200) 4096 1741)/2 = (5111287:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1740
  · change cPayment 1741 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1741+point (1327/200) 4096 1742)/2)
    have hp : cPayment 1741 = (75405642229:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1741+point (1327/200) 4096 1742)/2 = (5112341:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1741
  · change cPayment 1742 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1742+point (1327/200) 4096 1743)/2)
    have hp : cPayment 1742 = (75382918302:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1742+point (1327/200) 4096 1743)/2 = (1022679:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1742
  · change cPayment 1743 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1743+point (1327/200) 4096 1744)/2)
    have hp : cPayment 1743 = (75360170053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1743+point (1327/200) 4096 1744)/2 = (5114449:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1743
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_108
