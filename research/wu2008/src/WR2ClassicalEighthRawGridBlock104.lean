import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints104
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_104 (j : Fin 16) : upperValue ((point (16*104+j.val)+point ((16*104+j.val)+1))/2) ≤ payment (16*104+j.val) := by
  fin_cases j
  · change upperValue ((point (1664)+point ((1664)+1))/2) ≤ payment (1664)
    have hp : payment 1664 = (664111337449:ℝ)/1000000000000 := rfl
    have hx : (point 1664+point 1665)/2 = (4647683:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1664
  · change upperValue ((point (1665)+point ((1665)+1))/2) ≤ payment (1665)
    have hp : payment 1665 = (662315463058:ℝ)/1000000000000 := rfl
    have hx : (point 1665+point 1666)/2 = (4649737:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1665
  · change upperValue ((point (1666)+point ((1666)+1))/2) ≤ payment (1666)
    have hp : payment 1666 = (660520110579:ℝ)/1000000000000 := rfl
    have hx : (point 1666+point 1667)/2 = (1550597:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1666
  · change upperValue ((point (1667)+point ((1667)+1))/2) ≤ payment (1667)
    have hp : payment 1667 = (658725278405:ℝ)/1000000000000 := rfl
    have hx : (point 1667+point 1668)/2 = (4653845:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1667
  · change upperValue ((point (1668)+point ((1668)+1))/2) ≤ payment (1668)
    have hp : payment 1668 = (656930964932:ℝ)/1000000000000 := rfl
    have hx : (point 1668+point 1669)/2 = (4655899:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1668
  · change upperValue ((point (1669)+point ((1669)+1))/2) ≤ payment (1669)
    have hp : payment 1669 = (655137168555:ℝ)/1000000000000 := rfl
    have hx : (point 1669+point 1670)/2 = (1552651:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1669
  · change upperValue ((point (1670)+point ((1670)+1))/2) ≤ payment (1670)
    have hp : payment 1670 = (653343887674:ℝ)/1000000000000 := rfl
    have hx : (point 1670+point 1671)/2 = (4660007:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1670
  · change upperValue ((point (1671)+point ((1671)+1))/2) ≤ payment (1671)
    have hp : payment 1671 = (651551120691:ℝ)/1000000000000 := rfl
    have hx : (point 1671+point 1672)/2 = (4662061:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1671
  · change upperValue ((point (1672)+point ((1672)+1))/2) ≤ payment (1672)
    have hp : payment 1672 = (649758866007:ℝ)/1000000000000 := rfl
    have hx : (point 1672+point 1673)/2 = (1554705:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1672
  · change upperValue ((point (1673)+point ((1673)+1))/2) ≤ payment (1673)
    have hp : payment 1673 = (647967122026:ℝ)/1000000000000 := rfl
    have hx : (point 1673+point 1674)/2 = (4666169:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1673
  · change upperValue ((point (1674)+point ((1674)+1))/2) ≤ payment (1674)
    have hp : payment 1674 = (646175887155:ℝ)/1000000000000 := rfl
    have hx : (point 1674+point 1675)/2 = (4668223:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1674
  · change upperValue ((point (1675)+point ((1675)+1))/2) ≤ payment (1675)
    have hp : payment 1675 = (644385159803:ℝ)/1000000000000 := rfl
    have hx : (point 1675+point 1676)/2 = (1556759:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1675
  · change upperValue ((point (1676)+point ((1676)+1))/2) ≤ payment (1676)
    have hp : payment 1676 = (642594938377:ℝ)/1000000000000 := rfl
    have hx : (point 1676+point 1677)/2 = (4672331:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1676
  · change upperValue ((point (1677)+point ((1677)+1))/2) ≤ payment (1677)
    have hp : payment 1677 = (640805221291:ℝ)/1000000000000 := rfl
    have hx : (point 1677+point 1678)/2 = (4674385:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1677
  · change upperValue ((point (1678)+point ((1678)+1))/2) ≤ payment (1678)
    have hp : payment 1678 = (639016006958:ℝ)/1000000000000 := rfl
    have hx : (point 1678+point 1679)/2 = (1558813:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1678
  · change upperValue ((point (1679)+point ((1679)+1))/2) ≤ payment (1679)
    have hp : payment 1679 = (637227293792:ℝ)/1000000000000 := rfl
    have hx : (point 1679+point 1680)/2 = (4678493:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1679
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_104
