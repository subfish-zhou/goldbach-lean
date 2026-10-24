import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints110
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_110 (j : Fin 16) : upperValue ((point (16*110+j.val)+point ((16*110+j.val)+1))/2) ≤ payment (16*110+j.val) := by
  fin_cases j
  · change upperValue ((point (1760)+point ((1760)+1))/2) ≤ payment (1760)
    have hp : payment 1760 = (493863552841:ℝ)/1000000000000 := rfl
    have hx : (point 1760+point 1761)/2 = (4844867:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1760
  · change upperValue ((point (1761)+point ((1761)+1))/2) ≤ payment (1761)
    have hp : payment 1761 = (492110701463:ℝ)/1000000000000 := rfl
    have hx : (point 1761+point 1762)/2 = (4846921:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1761
  · change upperValue ((point (1762)+point ((1762)+1))/2) ≤ payment (1762)
    have hp : payment 1762 = (490358225418:ℝ)/1000000000000 := rfl
    have hx : (point 1762+point 1763)/2 = (1616325:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1762
  · change upperValue ((point (1763)+point ((1763)+1))/2) ≤ payment (1763)
    have hp : payment 1763 = (488606123254:ℝ)/1000000000000 := rfl
    have hx : (point 1763+point 1764)/2 = (4851029:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1763
  · change upperValue ((point (1764)+point ((1764)+1))/2) ≤ payment (1764)
    have hp : payment 1764 = (486854393517:ℝ)/1000000000000 := rfl
    have hx : (point 1764+point 1765)/2 = (4853083:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1764
  · change upperValue ((point (1765)+point ((1765)+1))/2) ≤ payment (1765)
    have hp : payment 1765 = (485103034759:ℝ)/1000000000000 := rfl
    have hx : (point 1765+point 1766)/2 = (1618379:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1765
  · change upperValue ((point (1766)+point ((1766)+1))/2) ≤ payment (1766)
    have hp : payment 1766 = (483352045530:ℝ)/1000000000000 := rfl
    have hx : (point 1766+point 1767)/2 = (4857191:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1766
  · change upperValue ((point (1767)+point ((1767)+1))/2) ≤ payment (1767)
    have hp : payment 1767 = (481601424383:ℝ)/1000000000000 := rfl
    have hx : (point 1767+point 1768)/2 = (4859245:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1767
  · change upperValue ((point (1768)+point ((1768)+1))/2) ≤ payment (1768)
    have hp : payment 1768 = (479851169871:ℝ)/1000000000000 := rfl
    have hx : (point 1768+point 1769)/2 = (1620433:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1768
  · change upperValue ((point (1769)+point ((1769)+1))/2) ≤ payment (1769)
    have hp : payment 1769 = (478101280550:ℝ)/1000000000000 := rfl
    have hx : (point 1769+point 1770)/2 = (4863353:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1769
  · change upperValue ((point (1770)+point ((1770)+1))/2) ≤ payment (1770)
    have hp : payment 1770 = (476351754977:ℝ)/1000000000000 := rfl
    have hx : (point 1770+point 1771)/2 = (4865407:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1770
  · change upperValue ((point (1771)+point ((1771)+1))/2) ≤ payment (1771)
    have hp : payment 1771 = (474602591708:ℝ)/1000000000000 := rfl
    have hx : (point 1771+point 1772)/2 = (1622487:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1771
  · change upperValue ((point (1772)+point ((1772)+1))/2) ≤ payment (1772)
    have hp : payment 1772 = (472853789304:ℝ)/1000000000000 := rfl
    have hx : (point 1772+point 1773)/2 = (4869515:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1772
  · change upperValue ((point (1773)+point ((1773)+1))/2) ≤ payment (1773)
    have hp : payment 1773 = (471105346324:ℝ)/1000000000000 := rfl
    have hx : (point 1773+point 1774)/2 = (4871569:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1773
  · change upperValue ((point (1774)+point ((1774)+1))/2) ≤ payment (1774)
    have hp : payment 1774 = (469357261331:ℝ)/1000000000000 := rfl
    have hx : (point 1774+point 1775)/2 = (1624541:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1774
  · change upperValue ((point (1775)+point ((1775)+1))/2) ≤ payment (1775)
    have hp : payment 1775 = (467609532888:ℝ)/1000000000000 := rfl
    have hx : (point 1775+point 1776)/2 = (4875677:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1775
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_110
