import WR2ClassicalEighthRawPayments
import WR2ClassicalEighthRawPoints125
noncomputable section
namespace WuPaper.ClassicalEighth
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem grid_block_125 (j : Fin 16) : upperValue ((point (16*125+j.val)+point ((16*125+j.val)+1))/2) ≤ payment (16*125+j.val) := by
  fin_cases j
  · change upperValue ((point (2000)+point ((2000)+1))/2) ≤ payment (2000)
    have hp : payment 2000 = (80796534724:ℝ)/1000000000000 := rfl
    have hx : (point 2000+point 2001)/2 = (5337827:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2000
  · change upperValue ((point (2001)+point ((2001)+1))/2) ≤ payment (2001)
    have hp : payment 2001 = (79094665313:ℝ)/1000000000000 := rfl
    have hx : (point 2001+point 2002)/2 = (5339881:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2001
  · change upperValue ((point (2002)+point ((2002)+1))/2) ≤ payment (2002)
    have hp : payment 2002 = (77392852808:ℝ)/1000000000000 := rfl
    have hx : (point 2002+point 2003)/2 = (1780645:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2002
  · change upperValue ((point (2003)+point ((2003)+1))/2) ≤ payment (2003)
    have hp : payment 2003 = (75691095976:ℝ)/1000000000000 := rfl
    have hx : (point 2003+point 2004)/2 = (5343989:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2003
  · change upperValue ((point (2004)+point ((2004)+1))/2) ≤ payment (2004)
    have hp : payment 2004 = (73989393582:ℝ)/1000000000000 := rfl
    have hx : (point 2004+point 2005)/2 = (5346043:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2004
  · change upperValue ((point (2005)+point ((2005)+1))/2) ≤ payment (2005)
    have hp : payment 2005 = (72287744394:ℝ)/1000000000000 := rfl
    have hx : (point 2005+point 2006)/2 = (1782699:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2005
  · change upperValue ((point (2006)+point ((2006)+1))/2) ≤ payment (2006)
    have hp : payment 2006 = (70586147179:ℝ)/1000000000000 := rfl
    have hx : (point 2006+point 2007)/2 = (5350151:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2006
  · change upperValue ((point (2007)+point ((2007)+1))/2) ≤ payment (2007)
    have hp : payment 2007 = (68884600704:ℝ)/1000000000000 := rfl
    have hx : (point 2007+point 2008)/2 = (5352205:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2007
  · change upperValue ((point (2008)+point ((2008)+1))/2) ≤ payment (2008)
    have hp : payment 2008 = (67183103738:ℝ)/1000000000000 := rfl
    have hx : (point 2008+point 2009)/2 = (1784753:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2008
  · change upperValue ((point (2009)+point ((2009)+1))/2) ≤ payment (2009)
    have hp : payment 2009 = (65481655050:ℝ)/1000000000000 := rfl
    have hx : (point 2009+point 2010)/2 = (5356313:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2009
  · change upperValue ((point (2010)+point ((2010)+1))/2) ≤ payment (2010)
    have hp : payment 2010 = (63780253409:ℝ)/1000000000000 := rfl
    have hx : (point 2010+point 2011)/2 = (5358367:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2010
  · change upperValue ((point (2011)+point ((2011)+1))/2) ≤ payment (2011)
    have hp : payment 2011 = (62078897584:ℝ)/1000000000000 := rfl
    have hx : (point 2011+point 2012)/2 = (1786807:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2011
  · change upperValue ((point (2012)+point ((2012)+1))/2) ≤ payment (2012)
    have hp : payment 2012 = (60377586346:ℝ)/1000000000000 := rfl
    have hx : (point 2012+point 2013)/2 = (5362475:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2012
  · change upperValue ((point (2013)+point ((2013)+1))/2) ≤ payment (2013)
    have hp : payment 2013 = (58676318465:ℝ)/1000000000000 := rfl
    have hx : (point 2013+point 2014)/2 = (5364529:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2013
  · change upperValue ((point (2014)+point ((2014)+1))/2) ≤ payment (2014)
    have hp : payment 2014 = (56975092713:ℝ)/1000000000000 := rfl
    have hx : (point 2014+point 2015)/2 = (1788861:ℝ)/5435392 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2014
  · change upperValue ((point (2015)+point ((2015)+1))/2) ≤ payment (2015)
    have hp : payment 2015 = (55273907861:ℝ)/1000000000000 := rfl
    have hx : (point 2015+point 2016)/2 = (5368637:ℝ)/16306176 := by norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
    rw [hp,hx]
    exact point_paid_2015
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.grid_block_125
