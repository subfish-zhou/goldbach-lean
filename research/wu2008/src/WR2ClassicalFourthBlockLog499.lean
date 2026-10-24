import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints499
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_499 (j : Fin 16) (hj : 16*499+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*499+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*499+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7984) ≤ val WuPaper.ClassicalFourthData.Bq 7984
    have hp : val WuPaper.ClassicalFourthData.Bq 7984 = (274594110524885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7984 = 274594110524885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7984 = (999:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7985) ≤ val WuPaper.ClassicalFourthData.Bq 7985
    have hp : val WuPaper.ClassicalFourthData.Bq 7985 = (274597812141115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7985 = 274597812141115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7985 = (3197:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7986) ≤ val WuPaper.ClassicalFourthData.Bq 7986
    have hp : val WuPaper.ClassicalFourthData.Bq 7986 = (274601511552253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7986 = 274601511552253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7986 = (7993:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7987) ≤ val WuPaper.ClassicalFourthData.Bq 7987
    have hp : val WuPaper.ClassicalFourthData.Bq 7987 = (274605208759006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7987 = 274605208759006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7987 = (15987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7988) ≤ val WuPaper.ClassicalFourthData.Bq 7988
    have hp : val WuPaper.ClassicalFourthData.Bq 7988 = (274608903762075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7988 = 274608903762075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7988 = (3997:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7989) ≤ val WuPaper.ClassicalFourthData.Bq 7989
    have hp : val WuPaper.ClassicalFourthData.Bq 7989 = (274612596562166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7989 = 274612596562166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7989 = (15989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7990) ≤ val WuPaper.ClassicalFourthData.Bq 7990
    have hp : val WuPaper.ClassicalFourthData.Bq 7990 = (274616287159983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7990 = 274616287159983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7990 = (1599:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7991) ≤ val WuPaper.ClassicalFourthData.Bq 7991
    have hp : val WuPaper.ClassicalFourthData.Bq 7991 = (274619975556228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7991 = 274619975556228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7991 = (15991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7991
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7992) ≤ val WuPaper.ClassicalFourthData.Bq 7992
    have hp : val WuPaper.ClassicalFourthData.Bq 7992 = (274623661751605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7992 = 274623661751605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7992 = (1999:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7993) ≤ val WuPaper.ClassicalFourthData.Bq 7993
    have hp : val WuPaper.ClassicalFourthData.Bq 7993 = (274627345746816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7993 = 274627345746816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7993 = (15993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7994) ≤ val WuPaper.ClassicalFourthData.Bq 7994
    have hp : val WuPaper.ClassicalFourthData.Bq 7994 = (274631027542565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7994 = 274631027542565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7994 = (7997:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7995) ≤ val WuPaper.ClassicalFourthData.Bq 7995
    have hp : val WuPaper.ClassicalFourthData.Bq 7995 = (274634707139554:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7995 = 274634707139554 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7995 = (3199:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7996) ≤ val WuPaper.ClassicalFourthData.Bq 7996
    have hp : val WuPaper.ClassicalFourthData.Bq 7996 = (274638384538485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7996 = 274638384538485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7996 = (3999:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7997) ≤ val WuPaper.ClassicalFourthData.Bq 7997
    have hp : val WuPaper.ClassicalFourthData.Bq 7997 = (274642059740060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7997 = 274642059740060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7997 = (15997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7998) ≤ val WuPaper.ClassicalFourthData.Bq 7998
    have hp : val WuPaper.ClassicalFourthData.Bq 7998 = (274645732744981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7998 = 274645732744981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7998 = (7999:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7999) ≤ val WuPaper.ClassicalFourthData.Bq 7999
    have hp : val WuPaper.ClassicalFourthData.Bq 7999 = (274649403553949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7999 = 274649403553949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7999 = (15999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_499
