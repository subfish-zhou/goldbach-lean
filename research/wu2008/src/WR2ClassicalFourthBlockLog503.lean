import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints503
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_503 (j : Fin 16) (hj : 16*503+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*503+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*503+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8048) ≤ val WuPaper.ClassicalFourthData.Bq 8048
    have hp : val WuPaper.ClassicalFourthData.Bq 8048 = (274826597692041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8048 = 274826597692041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8048 = (1003:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8049) ≤ val WuPaper.ClassicalFourthData.Bq 8049
    have hp : val WuPaper.ClassicalFourthData.Bq 8049 = (274830159592268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8049 = 274830159592268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8049 = (16049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8050) ≤ val WuPaper.ClassicalFourthData.Bq 8050
    have hp : val WuPaper.ClassicalFourthData.Bq 8050 = (274833719331989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8050 = 274833719331989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8050 = (321:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8051) ≤ val WuPaper.ClassicalFourthData.Bq 8051
    have hp : val WuPaper.ClassicalFourthData.Bq 8051 = (274837276911894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8051 = 274837276911894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8051 = (16051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8052) ≤ val WuPaper.ClassicalFourthData.Bq 8052
    have hp : val WuPaper.ClassicalFourthData.Bq 8052 = (274840832332671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8052 = 274840832332671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8052 = (4013:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8053) ≤ val WuPaper.ClassicalFourthData.Bq 8053
    have hp : val WuPaper.ClassicalFourthData.Bq 8053 = (274844385595008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8053 = 274844385595008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8053 = (16053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8054) ≤ val WuPaper.ClassicalFourthData.Bq 8054
    have hp : val WuPaper.ClassicalFourthData.Bq 8054 = (274847936699594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8054 = 274847936699594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8054 = (8027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8055) ≤ val WuPaper.ClassicalFourthData.Bq 8055
    have hp : val WuPaper.ClassicalFourthData.Bq 8055 = (274851485647115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8055 = 274851485647115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8055 = (3211:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8055
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8056) ≤ val WuPaper.ClassicalFourthData.Bq 8056
    have hp : val WuPaper.ClassicalFourthData.Bq 8056 = (274855032438259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8056 = 274855032438259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8056 = (2007:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8057) ≤ val WuPaper.ClassicalFourthData.Bq 8057
    have hp : val WuPaper.ClassicalFourthData.Bq 8057 = (274858577073715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8057 = 274858577073715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8057 = (16057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8058) ≤ val WuPaper.ClassicalFourthData.Bq 8058
    have hp : val WuPaper.ClassicalFourthData.Bq 8058 = (274862119554167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8058 = 274862119554167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8058 = (8029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8059) ≤ val WuPaper.ClassicalFourthData.Bq 8059
    have hp : val WuPaper.ClassicalFourthData.Bq 8059 = (274865659880305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8059 = 274865659880305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8059 = (16059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8060) ≤ val WuPaper.ClassicalFourthData.Bq 8060
    have hp : val WuPaper.ClassicalFourthData.Bq 8060 = (274869198052813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8060 = 274869198052813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8060 = (803:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8061) ≤ val WuPaper.ClassicalFourthData.Bq 8061
    have hp : val WuPaper.ClassicalFourthData.Bq 8061 = (274872734072378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8061 = 274872734072378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8061 = (16061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8062) ≤ val WuPaper.ClassicalFourthData.Bq 8062
    have hp : val WuPaper.ClassicalFourthData.Bq 8062 = (274876267939686:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8062 = 274876267939686 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8062 = (8031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8063) ≤ val WuPaper.ClassicalFourthData.Bq 8063
    have hp : val WuPaper.ClassicalFourthData.Bq 8063 = (274879799655424:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8063 = 274879799655424 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8063 = (16063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_503
