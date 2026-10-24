import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints109
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_109 (j : Fin 16) : upperValue ((point (16*109+j.val)+point ((16*109+j.val)+1))/2) ≤ payment (16*109+j.val) := by
  fin_cases j
  · change upperValue ((point (1744)+point ((1744)+1))/2) ≤ payment (1744)
    have hp : payment 1744 = (521961411225:ℝ)/1000000000000 := rfl
    have hx : (point 1744+point 1745)/2 = (1604001:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1744
  · change upperValue ((point (1745)+point ((1745)+1))/2) ≤ payment (1745)
    have hp : payment 1745 = (520202355773:ℝ)/1000000000000 := rfl
    have hx : (point 1745+point 1746)/2 = (4814057:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1745
  · change upperValue ((point (1746)+point ((1746)+1))/2) ≤ payment (1746)
    have hp : payment 1746 = (518443699092:ℝ)/1000000000000 := rfl
    have hx : (point 1746+point 1747)/2 = (4816111:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1746
  · change upperValue ((point (1747)+point ((1747)+1))/2) ≤ payment (1747)
    have hp : payment 1747 = (516685439707:ℝ)/1000000000000 := rfl
    have hx : (point 1747+point 1748)/2 = (1606055:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1747
  · change upperValue ((point (1748)+point ((1748)+1))/2) ≤ payment (1748)
    have hp : payment 1748 = (514927576143:ℝ)/1000000000000 := rfl
    have hx : (point 1748+point 1749)/2 = (4820219:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1748
  · change upperValue ((point (1749)+point ((1749)+1))/2) ≤ payment (1749)
    have hp : payment 1749 = (513170106929:ℝ)/1000000000000 := rfl
    have hx : (point 1749+point 1750)/2 = (4822273:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1749
  · change upperValue ((point (1750)+point ((1750)+1))/2) ≤ payment (1750)
    have hp : payment 1750 = (511413030592:ℝ)/1000000000000 := rfl
    have hx : (point 1750+point 1751)/2 = (1608109:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1750
  · change upperValue ((point (1751)+point ((1751)+1))/2) ≤ payment (1751)
    have hp : payment 1751 = (509656345663:ℝ)/1000000000000 := rfl
    have hx : (point 1751+point 1752)/2 = (4826381:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1751
  · change upperValue ((point (1752)+point ((1752)+1))/2) ≤ payment (1752)
    have hp : payment 1752 = (507900050673:ℝ)/1000000000000 := rfl
    have hx : (point 1752+point 1753)/2 = (4828435:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1752
  · change upperValue ((point (1753)+point ((1753)+1))/2) ≤ payment (1753)
    have hp : payment 1753 = (506144144156:ℝ)/1000000000000 := rfl
    have hx : (point 1753+point 1754)/2 = (1610163:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1753
  · change upperValue ((point (1754)+point ((1754)+1))/2) ≤ payment (1754)
    have hp : payment 1754 = (504388624647:ℝ)/1000000000000 := rfl
    have hx : (point 1754+point 1755)/2 = (4832543:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1754
  · change upperValue ((point (1755)+point ((1755)+1))/2) ≤ payment (1755)
    have hp : payment 1755 = (502633490680:ℝ)/1000000000000 := rfl
    have hx : (point 1755+point 1756)/2 = (4834597:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1755
  · change upperValue ((point (1756)+point ((1756)+1))/2) ≤ payment (1756)
    have hp : payment 1756 = (500878740793:ℝ)/1000000000000 := rfl
    have hx : (point 1756+point 1757)/2 = (1612217:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1756
  · change upperValue ((point (1757)+point ((1757)+1))/2) ≤ payment (1757)
    have hp : payment 1757 = (499124373525:ℝ)/1000000000000 := rfl
    have hx : (point 1757+point 1758)/2 = (4838705:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1757
  · change upperValue ((point (1758)+point ((1758)+1))/2) ≤ payment (1758)
    have hp : payment 1758 = (497370387416:ℝ)/1000000000000 := rfl
    have hx : (point 1758+point 1759)/2 = (4840759:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1758
  · change upperValue ((point (1759)+point ((1759)+1))/2) ≤ payment (1759)
    have hp : payment 1759 = (495616781007:ℝ)/1000000000000 := rfl
    have hx : (point 1759+point 1760)/2 = (1614271:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1759
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_109
