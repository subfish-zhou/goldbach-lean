import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints103
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_103 (j : Fin 16) : upperValue ((point (16*103+j.val)+point ((16*103+j.val)+1))/2) ≤ payment (16*103+j.val) := by
  fin_cases j
  · change upperValue ((point (1648)+point ((1648)+1))/2) ≤ payment (1648)
    have hp : payment 1648 = (692917625871:ℝ)/1000000000000 := rfl
    have hx : (point 1648+point 1649)/2 = (1538273:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1648
  · change upperValue ((point (1649)+point ((1649)+1))/2) ≤ payment (1649)
    have hp : payment 1649 = (691113180875:ℝ)/1000000000000 := rfl
    have hx : (point 1649+point 1650)/2 = (4616873:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1649
  · change upperValue ((point (1650)+point ((1650)+1))/2) ≤ payment (1650)
    have hp : payment 1650 = (689309283751:ℝ)/1000000000000 := rfl
    have hx : (point 1650+point 1651)/2 = (4618927:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1650
  · change upperValue ((point (1651)+point ((1651)+1))/2) ≤ payment (1651)
    have hp : payment 1651 = (687505932862:ℝ)/1000000000000 := rfl
    have hx : (point 1651+point 1652)/2 = (1540327:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1651
  · change upperValue ((point (1652)+point ((1652)+1))/2) ≤ payment (1652)
    have hp : payment 1652 = (685703126574:ℝ)/1000000000000 := rfl
    have hx : (point 1652+point 1653)/2 = (4623035:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1652
  · change upperValue ((point (1653)+point ((1653)+1))/2) ≤ payment (1653)
    have hp : payment 1653 = (683900863252:ℝ)/1000000000000 := rfl
    have hx : (point 1653+point 1654)/2 = (4625089:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1653
  · change upperValue ((point (1654)+point ((1654)+1))/2) ≤ payment (1654)
    have hp : payment 1654 = (682099141267:ℝ)/1000000000000 := rfl
    have hx : (point 1654+point 1655)/2 = (1542381:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1654
  · change upperValue ((point (1655)+point ((1655)+1))/2) ≤ payment (1655)
    have hp : payment 1655 = (680297958990:ℝ)/1000000000000 := rfl
    have hx : (point 1655+point 1656)/2 = (4629197:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1655
  · change upperValue ((point (1656)+point ((1656)+1))/2) ≤ payment (1656)
    have hp : payment 1656 = (678497314792:ℝ)/1000000000000 := rfl
    have hx : (point 1656+point 1657)/2 = (4631251:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1656
  · change upperValue ((point (1657)+point ((1657)+1))/2) ≤ payment (1657)
    have hp : payment 1657 = (676697207049:ℝ)/1000000000000 := rfl
    have hx : (point 1657+point 1658)/2 = (1544435:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1657
  · change upperValue ((point (1658)+point ((1658)+1))/2) ≤ payment (1658)
    have hp : payment 1658 = (674897634137:ℝ)/1000000000000 := rfl
    have hx : (point 1658+point 1659)/2 = (4635359:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1658
  · change upperValue ((point (1659)+point ((1659)+1))/2) ≤ payment (1659)
    have hp : payment 1659 = (673098594435:ℝ)/1000000000000 := rfl
    have hx : (point 1659+point 1660)/2 = (4637413:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1659
  · change upperValue ((point (1660)+point ((1660)+1))/2) ≤ payment (1660)
    have hp : payment 1660 = (671300086323:ℝ)/1000000000000 := rfl
    have hx : (point 1660+point 1661)/2 = (1546489:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1660
  · change upperValue ((point (1661)+point ((1661)+1))/2) ≤ payment (1661)
    have hp : payment 1661 = (669502108183:ℝ)/1000000000000 := rfl
    have hx : (point 1661+point 1662)/2 = (4641521:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1661
  · change upperValue ((point (1662)+point ((1662)+1))/2) ≤ payment (1662)
    have hp : payment 1662 = (667704658400:ℝ)/1000000000000 := rfl
    have hx : (point 1662+point 1663)/2 = (4643575:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1662
  · change upperValue ((point (1663)+point ((1663)+1))/2) ≤ payment (1663)
    have hp : payment 1663 = (665907735359:ℝ)/1000000000000 := rfl
    have hx : (point 1663+point 1664)/2 = (1548543:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1663
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_103
