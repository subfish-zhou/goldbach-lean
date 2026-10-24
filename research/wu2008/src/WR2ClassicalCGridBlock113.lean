import WR2ClassicalCPayments
import WR2ClassicalCPoints113
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_113 (j : Fin 16) : cPayment (16*113+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*113+j.val)+point (1327/200) 4096 (16*113+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1808 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1808+point (1327/200) 4096 1809)/2)
    have hp : cPayment 1808 = (73831222345:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1808+point (1327/200) 4096 1809)/2 = (5182959:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1808
  · change cPayment 1809 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1809+point (1327/200) 4096 1810)/2)
    have hp : cPayment 1809 = (73806953990:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1809+point (1327/200) 4096 1810)/2 = (5184013:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1809
  · change cPayment 1810 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1810+point (1327/200) 4096 1811)/2)
    have hp : cPayment 1810 = (73782663852:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1810+point (1327/200) 4096 1811)/2 = (5185067:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1810
  · change cPayment 1811 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1811+point (1327/200) 4096 1812)/2)
    have hp : cPayment 1811 = (73758351969:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1811+point (1327/200) 4096 1812)/2 = (5186121:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1811
  · change cPayment 1812 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1812+point (1327/200) 4096 1813)/2)
    have hp : cPayment 1812 = (73734018377:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1812+point (1327/200) 4096 1813)/2 = (207487:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1812
  · change cPayment 1813 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1813+point (1327/200) 4096 1814)/2)
    have hp : cPayment 1813 = (73709663111:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1813+point (1327/200) 4096 1814)/2 = (5188229:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1813
  · change cPayment 1814 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1814+point (1327/200) 4096 1815)/2)
    have hp : cPayment 1814 = (73685286208:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1814+point (1327/200) 4096 1815)/2 = (5189283:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1814
  · change cPayment 1815 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1815+point (1327/200) 4096 1816)/2)
    have hp : cPayment 1815 = (73660887703:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1815+point (1327/200) 4096 1816)/2 = (5190337:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1815
  · change cPayment 1816 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1816+point (1327/200) 4096 1817)/2)
    have hp : cPayment 1816 = (73636467633:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1816+point (1327/200) 4096 1817)/2 = (5191391:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1816
  · change cPayment 1817 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1817+point (1327/200) 4096 1818)/2)
    have hp : cPayment 1817 = (73612026033:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1817+point (1327/200) 4096 1818)/2 = (1038489:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1817
  · change cPayment 1818 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1818+point (1327/200) 4096 1819)/2)
    have hp : cPayment 1818 = (73587562940:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1818+point (1327/200) 4096 1819)/2 = (5193499:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1818
  · change cPayment 1819 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1819+point (1327/200) 4096 1820)/2)
    have hp : cPayment 1819 = (73563078388:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1819+point (1327/200) 4096 1820)/2 = (5194553:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1819
  · change cPayment 1820 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1820+point (1327/200) 4096 1821)/2)
    have hp : cPayment 1820 = (73538572414:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1820+point (1327/200) 4096 1821)/2 = (5195607:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1820
  · change cPayment 1821 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1821+point (1327/200) 4096 1822)/2)
    have hp : cPayment 1821 = (73514045053:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1821+point (1327/200) 4096 1822)/2 = (5196661:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1821
  · change cPayment 1822 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1822+point (1327/200) 4096 1823)/2)
    have hp : cPayment 1822 = (73489496341:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1822+point (1327/200) 4096 1823)/2 = (1039543:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1822
  · change cPayment 1823 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1823+point (1327/200) 4096 1824)/2)
    have hp : cPayment 1823 = (73464926313:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1823+point (1327/200) 4096 1824)/2 = (5198769:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1823
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_113
