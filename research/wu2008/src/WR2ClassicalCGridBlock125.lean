import WR2ClassicalCPayments
import WR2ClassicalCPoints125
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_125 (j : Fin 16) : cPayment (16*125+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*125+j.val)+point (1327/200) 4096 (16*125+j.val+1))/2) := by
  fin_cases j
  · change cPayment 2000 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2000+point (1327/200) 4096 2001)/2)
    have hp : cPayment 2000 = (68811696891:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2000+point (1327/200) 4096 2001)/2 = (5385327:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2000
  · change cPayment 2001 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2001+point (1327/200) 4096 2002)/2)
    have hp : cPayment 2001 = (68783855155:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2001+point (1327/200) 4096 2002)/2 = (5386381:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2001
  · change cPayment 2002 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2002+point (1327/200) 4096 2003)/2)
    have hp : cPayment 2002 = (68755997742:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2002+point (1327/200) 4096 2003)/2 = (1077487:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2002
  · change cPayment 2003 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2003+point (1327/200) 4096 2004)/2)
    have hp : cPayment 2003 = (68728124680:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2003+point (1327/200) 4096 2004)/2 = (5388489:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2003
  · change cPayment 2004 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2004+point (1327/200) 4096 2005)/2)
    have hp : cPayment 2004 = (68700235996:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2004+point (1327/200) 4096 2005)/2 = (5389543:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2004
  · change cPayment 2005 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2005+point (1327/200) 4096 2006)/2)
    have hp : cPayment 2005 = (68672331719:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2005+point (1327/200) 4096 2006)/2 = (5390597:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2005
  · change cPayment 2006 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2006+point (1327/200) 4096 2007)/2)
    have hp : cPayment 2006 = (68644411876:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2006+point (1327/200) 4096 2007)/2 = (5391651:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2006
  · change cPayment 2007 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2007+point (1327/200) 4096 2008)/2)
    have hp : cPayment 2007 = (68616476495:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2007+point (1327/200) 4096 2008)/2 = (1078541:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2007
  · change cPayment 2008 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2008+point (1327/200) 4096 2009)/2)
    have hp : cPayment 2008 = (68588525603:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2008+point (1327/200) 4096 2009)/2 = (5393759:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2008
  · change cPayment 2009 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2009+point (1327/200) 4096 2010)/2)
    have hp : cPayment 2009 = (68560559228:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2009+point (1327/200) 4096 2010)/2 = (5394813:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2009
  · change cPayment 2010 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2010+point (1327/200) 4096 2011)/2)
    have hp : cPayment 2010 = (68532577398:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2010+point (1327/200) 4096 2011)/2 = (5395867:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2010
  · change cPayment 2011 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2011+point (1327/200) 4096 2012)/2)
    have hp : cPayment 2011 = (68504580139:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2011+point (1327/200) 4096 2012)/2 = (5396921:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2011
  · change cPayment 2012 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2012+point (1327/200) 4096 2013)/2)
    have hp : cPayment 2012 = (68476567480:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2012+point (1327/200) 4096 2013)/2 = (215919:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2012
  · change cPayment 2013 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2013+point (1327/200) 4096 2014)/2)
    have hp : cPayment 2013 = (68448539447:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2013+point (1327/200) 4096 2014)/2 = (5399029:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2013
  · change cPayment 2014 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2014+point (1327/200) 4096 2015)/2)
    have hp : cPayment 2014 = (68420496068:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2014+point (1327/200) 4096 2015)/2 = (5400083:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2014
  · change cPayment 2015 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 2015+point (1327/200) 4096 2016)/2)
    have hp : cPayment 2015 = (68392437371:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 2015+point (1327/200) 4096 2016)/2 = (5401137:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_2015
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_125
