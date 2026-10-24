import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints565
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_565 (j : Fin 16) (hj : 16*565+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*565+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*565+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9040) ≤ val WuPaper.ClassicalFourthData.Bq 9040
    have hp : val WuPaper.ClassicalFourthData.Bq 9040 = (277400750093376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9040 = 277400750093376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9040 = (213:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9041) ≤ val WuPaper.ClassicalFourthData.Bq 9041
    have hp : val WuPaper.ClassicalFourthData.Bq 9041 = (277402471585957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9041 = 277402471585957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9041 = (17041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9042) ≤ val WuPaper.ClassicalFourthData.Bq 9042
    have hp : val WuPaper.ClassicalFourthData.Bq 9042 = (277404191496387:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9042 = 277404191496387 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9042 = (8521:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9043) ≤ val WuPaper.ClassicalFourthData.Bq 9043
    have hp : val WuPaper.ClassicalFourthData.Bq 9043 = (277405909825154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9043 = 277405909825154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9043 = (17043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9044) ≤ val WuPaper.ClassicalFourthData.Bq 9044
    have hp : val WuPaper.ClassicalFourthData.Bq 9044 = (277407626572750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9044 = 277407626572750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9044 = (4261:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9045) ≤ val WuPaper.ClassicalFourthData.Bq 9045
    have hp : val WuPaper.ClassicalFourthData.Bq 9045 = (277409341739663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9045 = 277409341739663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9045 = (3409:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9046) ≤ val WuPaper.ClassicalFourthData.Bq 9046
    have hp : val WuPaper.ClassicalFourthData.Bq 9046 = (277411055326384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9046 = 277411055326384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9046 = (8523:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9047) ≤ val WuPaper.ClassicalFourthData.Bq 9047
    have hp : val WuPaper.ClassicalFourthData.Bq 9047 = (277412767333403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9047 = 277412767333403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9047 = (17047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9047
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9048) ≤ val WuPaper.ClassicalFourthData.Bq 9048
    have hp : val WuPaper.ClassicalFourthData.Bq 9048 = (277414477761207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9048 = 277414477761207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9048 = (2131:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9049) ≤ val WuPaper.ClassicalFourthData.Bq 9049
    have hp : val WuPaper.ClassicalFourthData.Bq 9049 = (277416186610287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9049 = 277416186610287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9049 = (17049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9050) ≤ val WuPaper.ClassicalFourthData.Bq 9050
    have hp : val WuPaper.ClassicalFourthData.Bq 9050 = (277417893881132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9050 = 277417893881132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9050 = (341:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9051) ≤ val WuPaper.ClassicalFourthData.Bq 9051
    have hp : val WuPaper.ClassicalFourthData.Bq 9051 = (277419599574230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9051 = 277419599574230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9051 = (17051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9052) ≤ val WuPaper.ClassicalFourthData.Bq 9052
    have hp : val WuPaper.ClassicalFourthData.Bq 9052 = (277421303690069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9052 = 277421303690069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9052 = (4263:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9053) ≤ val WuPaper.ClassicalFourthData.Bq 9053
    have hp : val WuPaper.ClassicalFourthData.Bq 9053 = (277423006229140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9053 = 277423006229140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9053 = (17053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9054) ≤ val WuPaper.ClassicalFourthData.Bq 9054
    have hp : val WuPaper.ClassicalFourthData.Bq 9054 = (277424707191929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9054 = 277424707191929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9054 = (8527:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9055) ≤ val WuPaper.ClassicalFourthData.Bq 9055
    have hp : val WuPaper.ClassicalFourthData.Bq 9055 = (277426406578924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9055 = 277426406578924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9055 = (3411:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_565
