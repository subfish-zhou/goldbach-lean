import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints105
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_105 (j : Fin 16) : upperValue ((point (16*105+j.val)+point ((16*105+j.val)+1))/2) ≤ payment (16*105+j.val) := by
  fin_cases j
  · change upperValue ((point (1680)+point ((1680)+1))/2) ≤ payment (1680)
    have hp : payment 1680 = (635439080210:ℝ)/1000000000000 := rfl
    have hx : (point 1680+point 1681)/2 = (4680547:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1680
  · change upperValue ((point (1681)+point ((1681)+1))/2) ≤ payment (1681)
    have hp : payment 1681 = (633651364632:ℝ)/1000000000000 := rfl
    have hx : (point 1681+point 1682)/2 = (1560867:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1681
  · change upperValue ((point (1682)+point ((1682)+1))/2) ≤ payment (1682)
    have hp : payment 1682 = (631864145477:ℝ)/1000000000000 := rfl
    have hx : (point 1682+point 1683)/2 = (4684655:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1682
  · change upperValue ((point (1683)+point ((1683)+1))/2) ≤ payment (1683)
    have hp : payment 1683 = (630077421168:ℝ)/1000000000000 := rfl
    have hx : (point 1683+point 1684)/2 = (4686709:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1683
  · change upperValue ((point (1684)+point ((1684)+1))/2) ≤ payment (1684)
    have hp : payment 1684 = (628291190129:ℝ)/1000000000000 := rfl
    have hx : (point 1684+point 1685)/2 = (1562921:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1684
  · change upperValue ((point (1685)+point ((1685)+1))/2) ≤ payment (1685)
    have hp : payment 1685 = (626505450785:ℝ)/1000000000000 := rfl
    have hx : (point 1685+point 1686)/2 = (4690817:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1685
  · change upperValue ((point (1686)+point ((1686)+1))/2) ≤ payment (1686)
    have hp : payment 1686 = (624720201564:ℝ)/1000000000000 := rfl
    have hx : (point 1686+point 1687)/2 = (4692871:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1686
  · change upperValue ((point (1687)+point ((1687)+1))/2) ≤ payment (1687)
    have hp : payment 1687 = (622935440895:ℝ)/1000000000000 := rfl
    have hx : (point 1687+point 1688)/2 = (1564975:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1687
  · change upperValue ((point (1688)+point ((1688)+1))/2) ≤ payment (1688)
    have hp : payment 1688 = (621151167209:ℝ)/1000000000000 := rfl
    have hx : (point 1688+point 1689)/2 = (4696979:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1688
  · change upperValue ((point (1689)+point ((1689)+1))/2) ≤ payment (1689)
    have hp : payment 1689 = (619367378938:ℝ)/1000000000000 := rfl
    have hx : (point 1689+point 1690)/2 = (4699033:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1689
  · change upperValue ((point (1690)+point ((1690)+1))/2) ≤ payment (1690)
    have hp : payment 1690 = (617584074517:ℝ)/1000000000000 := rfl
    have hx : (point 1690+point 1691)/2 = (1567029:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1690
  · change upperValue ((point (1691)+point ((1691)+1))/2) ≤ payment (1691)
    have hp : payment 1691 = (615801252383:ℝ)/1000000000000 := rfl
    have hx : (point 1691+point 1692)/2 = (4703141:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1691
  · change upperValue ((point (1692)+point ((1692)+1))/2) ≤ payment (1692)
    have hp : payment 1692 = (614018910972:ℝ)/1000000000000 := rfl
    have hx : (point 1692+point 1693)/2 = (4705195:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1692
  · change upperValue ((point (1693)+point ((1693)+1))/2) ≤ payment (1693)
    have hp : payment 1693 = (612237048724:ℝ)/1000000000000 := rfl
    have hx : (point 1693+point 1694)/2 = (1569083:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1693
  · change upperValue ((point (1694)+point ((1694)+1))/2) ≤ payment (1694)
    have hp : payment 1694 = (610455664081:ℝ)/1000000000000 := rfl
    have hx : (point 1694+point 1695)/2 = (4709303:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1694
  · change upperValue ((point (1695)+point ((1695)+1))/2) ≤ payment (1695)
    have hp : payment 1695 = (608674755485:ℝ)/1000000000000 := rfl
    have hx : (point 1695+point 1696)/2 = (4711357:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1695
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_105
