import WR2ClassicalCPayments
import WR2ClassicalCPoints124
noncomputable section
namespace WuPaper.ClassicalC
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem c_grid_block_124 (j : Fin 16) : cPayment (16*124+j.val) ≤
    lowerKernel 1 (1327/200)
      ((point (1327/200) 4096 (16*124+j.val)+point (1327/200) 4096 (16*124+j.val+1))/2) := by
  fin_cases j
  · change cPayment 1984 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1984+point (1327/200) 4096 1985)/2)
    have hp : cPayment 1984 = (69255009798:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1984+point (1327/200) 4096 1985)/2 = (5368463:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1984
  · change cPayment 1985 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1985+point (1327/200) 4096 1986)/2)
    have hp : cPayment 1985 = (69227422701:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1985+point (1327/200) 4096 1986)/2 = (5369517:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1985
  · change cPayment 1986 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1986+point (1327/200) 4096 1987)/2)
    have hp : cPayment 1986 = (69199819478:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1986+point (1327/200) 4096 1987)/2 = (5370571:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1986
  · change cPayment 1987 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1987+point (1327/200) 4096 1988)/2)
    have hp : cPayment 1987 = (69172200156:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1987+point (1327/200) 4096 1988)/2 = (214865:ℝ)/65536 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1987
  · change cPayment 1988 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1988+point (1327/200) 4096 1989)/2)
    have hp : cPayment 1988 = (69144564765:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1988+point (1327/200) 4096 1989)/2 = (5372679:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1988
  · change cPayment 1989 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1989+point (1327/200) 4096 1990)/2)
    have hp : cPayment 1989 = (69116913332:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1989+point (1327/200) 4096 1990)/2 = (5373733:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1989
  · change cPayment 1990 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1990+point (1327/200) 4096 1991)/2)
    have hp : cPayment 1990 = (69089245886:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1990+point (1327/200) 4096 1991)/2 = (5374787:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1990
  · change cPayment 1991 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1991+point (1327/200) 4096 1992)/2)
    have hp : cPayment 1991 = (69061562455:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1991+point (1327/200) 4096 1992)/2 = (5375841:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1991
  · change cPayment 1992 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1992+point (1327/200) 4096 1993)/2)
    have hp : cPayment 1992 = (69033863067:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1992+point (1327/200) 4096 1993)/2 = (1075379:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1992
  · change cPayment 1993 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1993+point (1327/200) 4096 1994)/2)
    have hp : cPayment 1993 = (69006147750:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1993+point (1327/200) 4096 1994)/2 = (5377949:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1993
  · change cPayment 1994 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1994+point (1327/200) 4096 1995)/2)
    have hp : cPayment 1994 = (68978416533:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1994+point (1327/200) 4096 1995)/2 = (5379003:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1994
  · change cPayment 1995 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1995+point (1327/200) 4096 1996)/2)
    have hp : cPayment 1995 = (68950669444:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1995+point (1327/200) 4096 1996)/2 = (5380057:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1995
  · change cPayment 1996 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1996+point (1327/200) 4096 1997)/2)
    have hp : cPayment 1996 = (68922906510:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1996+point (1327/200) 4096 1997)/2 = (5381111:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1996
  · change cPayment 1997 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1997+point (1327/200) 4096 1998)/2)
    have hp : cPayment 1997 = (68895127760:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1997+point (1327/200) 4096 1998)/2 = (1076433:ℝ)/327680 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1997
  · change cPayment 1998 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1998+point (1327/200) 4096 1999)/2)
    have hp : cPayment 1998 = (68867333221:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1998+point (1327/200) 4096 1999)/2 = (5383219:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1998
  · change cPayment 1999 ≤ lowerKernel 1 (1327/200) ((point (1327/200) 4096 1999+point (1327/200) 4096 2000)/2)
    have hp : cPayment 1999 = (68839522922:ℝ)/1000000000000 := by
      rfl
    have hx : (point (1327/200) 4096 1999+point (1327/200) 4096 2000)/2 = (5384273:ℝ)/1638400 := by
      norm_num [point,step]
    rw [hp,hx]
    exact midpoint_paid_1999
end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.c_grid_block_124
