import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints107
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_107 (j : Fin 16) : upperValue ((point (16*107+j.val)+point ((16*107+j.val)+1))/2) ≤ payment (16*107+j.val) := by
  fin_cases j
  · change upperValue ((point (1712)+point ((1712)+1))/2) ≤ payment (1712)
    have hp : payment 1712 = (578470643910:ℝ)/1000000000000 := rfl
    have hx : (point 1712+point 1713)/2 = (4746275:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1712
  · change upperValue ((point (1713)+point ((1713)+1))/2) ≤ payment (1713)
    have hp : payment 1713 = (576698039809:ℝ)/1000000000000 := rfl
    have hx : (point 1713+point 1714)/2 = (4748329:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1713
  · change upperValue ((point (1714)+point ((1714)+1))/2) ≤ payment (1714)
    have hp : payment 1714 = (574925882488:ℝ)/1000000000000 := rfl
    have hx : (point 1714+point 1715)/2 = (1583461:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1714
  · change upperValue ((point (1715)+point ((1715)+1))/2) ≤ payment (1715)
    have hp : payment 1715 = (573154170420:ℝ)/1000000000000 := rfl
    have hx : (point 1715+point 1716)/2 = (4752437:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1715
  · change upperValue ((point (1716)+point ((1716)+1))/2) ≤ payment (1716)
    have hp : payment 1716 = (571382902085:ℝ)/1000000000000 := rfl
    have hx : (point 1716+point 1717)/2 = (4754491:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1716
  · change upperValue ((point (1717)+point ((1717)+1))/2) ≤ payment (1717)
    have hp : payment 1717 = (569612075960:ℝ)/1000000000000 := rfl
    have hx : (point 1717+point 1718)/2 = (1585515:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1717
  · change upperValue ((point (1718)+point ((1718)+1))/2) ≤ payment (1718)
    have hp : payment 1718 = (567841690526:ℝ)/1000000000000 := rfl
    have hx : (point 1718+point 1719)/2 = (4758599:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1718
  · change upperValue ((point (1719)+point ((1719)+1))/2) ≤ payment (1719)
    have hp : payment 1719 = (566071744266:ℝ)/1000000000000 := rfl
    have hx : (point 1719+point 1720)/2 = (4760653:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1719
  · change upperValue ((point (1720)+point ((1720)+1))/2) ≤ payment (1720)
    have hp : payment 1720 = (564302235663:ℝ)/1000000000000 := rfl
    have hx : (point 1720+point 1721)/2 = (1587569:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1720
  · change upperValue ((point (1721)+point ((1721)+1))/2) ≤ payment (1721)
    have hp : payment 1721 = (562533163203:ℝ)/1000000000000 := rfl
    have hx : (point 1721+point 1722)/2 = (4764761:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1721
  · change upperValue ((point (1722)+point ((1722)+1))/2) ≤ payment (1722)
    have hp : payment 1722 = (560764525372:ℝ)/1000000000000 := rfl
    have hx : (point 1722+point 1723)/2 = (4766815:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1722
  · change upperValue ((point (1723)+point ((1723)+1))/2) ≤ payment (1723)
    have hp : payment 1723 = (558996320659:ℝ)/1000000000000 := rfl
    have hx : (point 1723+point 1724)/2 = (1589623:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1723
  · change upperValue ((point (1724)+point ((1724)+1))/2) ≤ payment (1724)
    have hp : payment 1724 = (557228547554:ℝ)/1000000000000 := rfl
    have hx : (point 1724+point 1725)/2 = (4770923:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1724
  · change upperValue ((point (1725)+point ((1725)+1))/2) ≤ payment (1725)
    have hp : payment 1725 = (555461204548:ℝ)/1000000000000 := rfl
    have hx : (point 1725+point 1726)/2 = (4772977:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1725
  · change upperValue ((point (1726)+point ((1726)+1))/2) ≤ payment (1726)
    have hp : payment 1726 = (553694290134:ℝ)/1000000000000 := rfl
    have hx : (point 1726+point 1727)/2 = (1591677:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1726
  · change upperValue ((point (1727)+point ((1727)+1))/2) ≤ payment (1727)
    have hp : payment 1727 = (551927802807:ℝ)/1000000000000 := rfl
    have hx : (point 1727+point 1728)/2 = (4777085:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1727
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_107
