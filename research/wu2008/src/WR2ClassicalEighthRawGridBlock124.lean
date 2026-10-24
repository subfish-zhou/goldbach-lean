import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints124
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_124 (j : Fin 16) : upperValue ((point (16*124+j.val)+point ((16*124+j.val)+1))/2) ≤ payment (16*124+j.val) := by
  fin_cases j
  · change upperValue ((point (1984)+point ((1984)+1))/2) ≤ payment (1984)
    have hp : payment 1984 = (108035193726:ℝ)/1000000000000 := rfl
    have hx : (point 1984+point 1985)/2 = (1768321:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1984
  · change upperValue ((point (1985)+point ((1985)+1))/2) ≤ payment (1985)
    have hp : payment 1985 = (106332245533:ℝ)/1000000000000 := rfl
    have hx : (point 1985+point 1986)/2 = (5307017:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1985
  · change upperValue ((point (1986)+point ((1986)+1))/2) ≤ payment (1986)
    have hp : payment 1986 = (104629374065:ℝ)/1000000000000 := rfl
    have hx : (point 1986+point 1987)/2 = (5309071:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1986
  · change upperValue ((point (1987)+point ((1987)+1))/2) ≤ payment (1987)
    have hp : payment 1987 = (102926578079:ℝ)/1000000000000 := rfl
    have hx : (point 1987+point 1988)/2 = (1770375:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1987
  · change upperValue ((point (1988)+point ((1988)+1))/2) ≤ payment (1988)
    have hp : payment 1988 = (101223856334:ℝ)/1000000000000 := rfl
    have hx : (point 1988+point 1989)/2 = (5313179:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1988
  · change upperValue ((point (1989)+point ((1989)+1))/2) ≤ payment (1989)
    have hp : payment 1989 = (99521207587:ℝ)/1000000000000 := rfl
    have hx : (point 1989+point 1990)/2 = (5315233:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1989
  · change upperValue ((point (1990)+point ((1990)+1))/2) ≤ payment (1990)
    have hp : payment 1990 = (97818630597:ℝ)/1000000000000 := rfl
    have hx : (point 1990+point 1991)/2 = (1772429:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1990
  · change upperValue ((point (1991)+point ((1991)+1))/2) ≤ payment (1991)
    have hp : payment 1991 = (96116124125:ℝ)/1000000000000 := rfl
    have hx : (point 1991+point 1992)/2 = (5319341:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1991
  · change upperValue ((point (1992)+point ((1992)+1))/2) ≤ payment (1992)
    have hp : payment 1992 = (94413686929:ℝ)/1000000000000 := rfl
    have hx : (point 1992+point 1993)/2 = (5321395:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1992
  · change upperValue ((point (1993)+point ((1993)+1))/2) ≤ payment (1993)
    have hp : payment 1993 = (92711317772:ℝ)/1000000000000 := rfl
    have hx : (point 1993+point 1994)/2 = (1774483:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1993
  · change upperValue ((point (1994)+point ((1994)+1))/2) ≤ payment (1994)
    have hp : payment 1994 = (91009015413:ℝ)/1000000000000 := rfl
    have hx : (point 1994+point 1995)/2 = (5325503:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1994
  · change upperValue ((point (1995)+point ((1995)+1))/2) ≤ payment (1995)
    have hp : payment 1995 = (89306778614:ℝ)/1000000000000 := rfl
    have hx : (point 1995+point 1996)/2 = (5327557:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1995
  · change upperValue ((point (1996)+point ((1996)+1))/2) ≤ payment (1996)
    have hp : payment 1996 = (87604606139:ℝ)/1000000000000 := rfl
    have hx : (point 1996+point 1997)/2 = (1776537:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1996
  · change upperValue ((point (1997)+point ((1997)+1))/2) ≤ payment (1997)
    have hp : payment 1997 = (85902496748:ℝ)/1000000000000 := rfl
    have hx : (point 1997+point 1998)/2 = (5331665:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1997
  · change upperValue ((point (1998)+point ((1998)+1))/2) ≤ payment (1998)
    have hp : payment 1998 = (84200449206:ℝ)/1000000000000 := rfl
    have hx : (point 1998+point 1999)/2 = (5333719:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1998
  · change upperValue ((point (1999)+point ((1999)+1))/2) ≤ payment (1999)
    have hp : payment 1999 = (82498462277:ℝ)/1000000000000 := rfl
    have hx : (point 1999+point 2000)/2 = (1778591:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_1999
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_124
