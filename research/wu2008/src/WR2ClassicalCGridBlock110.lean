import WR2ClassicalCPayments
import WR2ClassicalCPoints110
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_110 (j : Fin 16) : cPayment (16*110+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*110+j.val)+point (1327/200) 4096 (16*110+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1760 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1760+point (1327/200) 4096 1761)/2)
    have hp : cPayment 1760 = (74969766773:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1760+point (1327/200) 4096 1761)/2 = (5132367:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1760
  · change cPayment 1761 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1761+point (1327/200) 4096 1762)/2)
    have hp : cPayment 1761 = (74946587459:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1761+point (1327/200) 4096 1762)/2 = (5133421:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1761
  · change cPayment 1762 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1762+point (1327/200) 4096 1763)/2)
    have hp : cPayment 1762 = (74923384566:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1762+point (1327/200) 4096 1763)/2 = (205379:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1762
  · change cPayment 1763 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1763+point (1327/200) 4096 1764)/2)
    have hp : cPayment 1763 = (74900158135:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1763+point (1327/200) 4096 1764)/2 = (5135529:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1763
  · change cPayment 1764 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1764+point (1327/200) 4096 1765)/2)
    have hp : cPayment 1764 = (74876908204:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1764+point (1327/200) 4096 1765)/2 = (5136583:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1764
  · change cPayment 1765 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1765+point (1327/200) 4096 1766)/2)
    have hp : cPayment 1765 = (74853634811:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1765+point (1327/200) 4096 1766)/2 = (5137637:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1765
  · change cPayment 1766 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1766+point (1327/200) 4096 1767)/2)
    have hp : cPayment 1766 = (74830337994:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1766+point (1327/200) 4096 1767)/2 = (5138691:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1766
  · change cPayment 1767 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1767+point (1327/200) 4096 1768)/2)
    have hp : cPayment 1767 = (74807017793:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1767+point (1327/200) 4096 1768)/2 = (1027949:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1767
  · change cPayment 1768 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1768+point (1327/200) 4096 1769)/2)
    have hp : cPayment 1768 = (74783674245:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1768+point (1327/200) 4096 1769)/2 = (5140799:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1768
  · change cPayment 1769 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1769+point (1327/200) 4096 1770)/2)
    have hp : cPayment 1769 = (74760307389:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1769+point (1327/200) 4096 1770)/2 = (5141853:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1769
  · change cPayment 1770 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1770+point (1327/200) 4096 1771)/2)
    have hp : cPayment 1770 = (74736917264:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1770+point (1327/200) 4096 1771)/2 = (5142907:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1770
  · change cPayment 1771 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1771+point (1327/200) 4096 1772)/2)
    have hp : cPayment 1771 = (74713503906:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1771+point (1327/200) 4096 1772)/2 = (5143961:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1771
  · change cPayment 1772 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1772+point (1327/200) 4096 1773)/2)
    have hp : cPayment 1772 = (74690067356:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1772+point (1327/200) 4096 1773)/2 = (1029003:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1772
  · change cPayment 1773 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1773+point (1327/200) 4096 1774)/2)
    have hp : cPayment 1773 = (74666607650:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1773+point (1327/200) 4096 1774)/2 = (5146069:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1773
  · change cPayment 1774 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1774+point (1327/200) 4096 1775)/2)
    have hp : cPayment 1774 = (74643124826:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1774+point (1327/200) 4096 1775)/2 = (5147123:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1774
  · change cPayment 1775 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1775+point (1327/200) 4096 1776)/2)
    have hp : cPayment 1775 = (74619618924:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1775+point (1327/200) 4096 1776)/2 = (5148177:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1775
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_110
