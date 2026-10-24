import WR2ClassicalCPayments
import WR2ClassicalCPoints107
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_107 (j : Fin 16) : cPayment (16*107+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*107+j.val)+point (1327/200) 4096 (16*107+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1712 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1712+point (1327/200) 4096 1713)/2)
    have hp : cPayment 1712 = (76053875585:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1712+point (1327/200) 4096 1713)/2 = (203271:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1712
  · change cPayment 1713 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1713+point (1327/200) 4096 1714)/2)
    have hp : cPayment 1713 = (76031874514:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1713+point (1327/200) 4096 1714)/2 = (5082829:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1713
  · change cPayment 1714 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1714+point (1327/200) 4096 1715)/2)
    have hp : cPayment 1714 = (76009847947:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1714+point (1327/200) 4096 1715)/2 = (5083883:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1714
  · change cPayment 1715 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1715+point (1327/200) 4096 1716)/2)
    have hp : cPayment 1715 = (75987795923:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1715+point (1327/200) 4096 1716)/2 = (5084937:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1715
  · change cPayment 1716 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1716+point (1327/200) 4096 1717)/2)
    have hp : cPayment 1716 = (75965718484:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1716+point (1327/200) 4096 1717)/2 = (5085991:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1716
  · change cPayment 1717 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1717+point (1327/200) 4096 1718)/2)
    have hp : cPayment 1717 = (75943615672:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1717+point (1327/200) 4096 1718)/2 = (1017409:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1717
  · change cPayment 1718 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1718+point (1327/200) 4096 1719)/2)
    have hp : cPayment 1718 = (75921487527:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1718+point (1327/200) 4096 1719)/2 = (5088099:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1718
  · change cPayment 1719 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1719+point (1327/200) 4096 1720)/2)
    have hp : cPayment 1719 = (75899334091:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1719+point (1327/200) 4096 1720)/2 = (5089153:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1719
  · change cPayment 1720 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1720+point (1327/200) 4096 1721)/2)
    have hp : cPayment 1720 = (75877155404:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1720+point (1327/200) 4096 1721)/2 = (5090207:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1720
  · change cPayment 1721 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1721+point (1327/200) 4096 1722)/2)
    have hp : cPayment 1721 = (75854951509:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1721+point (1327/200) 4096 1722)/2 = (5091261:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1721
  · change cPayment 1722 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1722+point (1327/200) 4096 1723)/2)
    have hp : cPayment 1722 = (75832722444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1722+point (1327/200) 4096 1723)/2 = (1018463:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1722
  · change cPayment 1723 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1723+point (1327/200) 4096 1724)/2)
    have hp : cPayment 1723 = (75810468252:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1723+point (1327/200) 4096 1724)/2 = (5093369:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1723
  · change cPayment 1724 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1724+point (1327/200) 4096 1725)/2)
    have hp : cPayment 1724 = (75788188974:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1724+point (1327/200) 4096 1725)/2 = (5094423:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1724
  · change cPayment 1725 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1725+point (1327/200) 4096 1726)/2)
    have hp : cPayment 1725 = (75765884649:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1725+point (1327/200) 4096 1726)/2 = (5095477:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1725
  · change cPayment 1726 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1726+point (1327/200) 4096 1727)/2)
    have hp : cPayment 1726 = (75743555319:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1726+point (1327/200) 4096 1727)/2 = (5096531:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1726
  · change cPayment 1727 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1727+point (1327/200) 4096 1728)/2)
    have hp : cPayment 1727 = (75721201024:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1727+point (1327/200) 4096 1728)/2 = (1019517:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1727
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_107
