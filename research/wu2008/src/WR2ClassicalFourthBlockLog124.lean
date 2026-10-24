import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints124
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_124 (j : Fin 16) (hj : 16*124+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*124+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*124+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1984) ≤ val WuPaper.ClassicalFourthData.Bq 1984
    have hp : val WuPaper.ClassicalFourthData.Bq 1984 = (161376153666782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1984 = 161376153666782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1984 = (312:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1985) ≤ val WuPaper.ClassicalFourthData.Bq 1985
    have hp : val WuPaper.ClassicalFourthData.Bq 1985 = (161426931553349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1985 = 161426931553349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1985 = (1997:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1986) ≤ val WuPaper.ClassicalFourthData.Bq 1986
    have hp : val WuPaper.ClassicalFourthData.Bq 1986 = (161477688087570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1986 = 161477688087570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1986 = (4993:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1987) ≤ val WuPaper.ClassicalFourthData.Bq 1987
    have hp : val WuPaper.ClassicalFourthData.Bq 1987 = (161528423279594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1987 = 161528423279594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1987 = (9987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1988) ≤ val WuPaper.ClassicalFourthData.Bq 1988
    have hp : val WuPaper.ClassicalFourthData.Bq 1988 = (161579137139564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1988 = 161579137139564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1988 = (2497:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1989) ≤ val WuPaper.ClassicalFourthData.Bq 1989
    have hp : val WuPaper.ClassicalFourthData.Bq 1989 = (161629829677620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1989 = 161629829677620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1989 = (9989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1990) ≤ val WuPaper.ClassicalFourthData.Bq 1990
    have hp : val WuPaper.ClassicalFourthData.Bq 1990 = (161680500903891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1990 = 161680500903891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1990 = (999:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1991) ≤ val WuPaper.ClassicalFourthData.Bq 1991
    have hp : val WuPaper.ClassicalFourthData.Bq 1991 = (161731150828505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1991 = 161731150828505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1991 = (9991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1991
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1992) ≤ val WuPaper.ClassicalFourthData.Bq 1992
    have hp : val WuPaper.ClassicalFourthData.Bq 1992 = (161781779461581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1992 = 161781779461581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1992 = (1249:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1993) ≤ val WuPaper.ClassicalFourthData.Bq 1993
    have hp : val WuPaper.ClassicalFourthData.Bq 1993 = (161832386813233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1993 = 161832386813233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1993 = (9993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1994) ≤ val WuPaper.ClassicalFourthData.Bq 1994
    have hp : val WuPaper.ClassicalFourthData.Bq 1994 = (161882972893569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1994 = 161882972893569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1994 = (4997:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1995) ≤ val WuPaper.ClassicalFourthData.Bq 1995
    have hp : val WuPaper.ClassicalFourthData.Bq 1995 = (161933537712692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1995 = 161933537712692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1995 = (1999:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1996) ≤ val WuPaper.ClassicalFourthData.Bq 1996
    have hp : val WuPaper.ClassicalFourthData.Bq 1996 = (161984081280697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1996 = 161984081280697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1996 = (2499:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1997) ≤ val WuPaper.ClassicalFourthData.Bq 1997
    have hp : val WuPaper.ClassicalFourthData.Bq 1997 = (162034603607676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1997 = 162034603607676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1997 = (9997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1998) ≤ val WuPaper.ClassicalFourthData.Bq 1998
    have hp : val WuPaper.ClassicalFourthData.Bq 1998 = (162085104703712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1998 = 162085104703712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1998 = (4999:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1999) ≤ val WuPaper.ClassicalFourthData.Bq 1999
    have hp : val WuPaper.ClassicalFourthData.Bq 1999 = (162135584578885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1999 = 162135584578885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1999 = (9999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_124
