import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints567
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_567 (j : Fin 16) (hj : 16*567+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*567+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*567+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9072) ≤ val WuPaper.ClassicalFourthData.Bq 9072
    have hp : val WuPaper.ClassicalFourthData.Bq 9072 = (277455055533751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9072 = 277455055533751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9072 = (1067:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9073) ≤ val WuPaper.ClassicalFourthData.Bq 9073
    have hp : val WuPaper.ClassicalFourthData.Bq 9073 = (277456726639761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9073 = 277456726639761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9073 = (17073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9074) ≤ val WuPaper.ClassicalFourthData.Bq 9074
    have hp : val WuPaper.ClassicalFourthData.Bq 9074 = (277458396179223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9074 = 277458396179223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9074 = (8537:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9075) ≤ val WuPaper.ClassicalFourthData.Bq 9075
    have hp : val WuPaper.ClassicalFourthData.Bq 9075 = (277460064152620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9075 = 277460064152620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9075 = (683:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9076) ≤ val WuPaper.ClassicalFourthData.Bq 9076
    have hp : val WuPaper.ClassicalFourthData.Bq 9076 = (277461730560438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9076 = 277461730560438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9076 = (4269:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9077) ≤ val WuPaper.ClassicalFourthData.Bq 9077
    have hp : val WuPaper.ClassicalFourthData.Bq 9077 = (277463395403162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9077 = 277463395403162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9077 = (17077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9078) ≤ val WuPaper.ClassicalFourthData.Bq 9078
    have hp : val WuPaper.ClassicalFourthData.Bq 9078 = (277465058681275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9078 = 277465058681275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9078 = (8539:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9079) ≤ val WuPaper.ClassicalFourthData.Bq 9079
    have hp : val WuPaper.ClassicalFourthData.Bq 9079 = (277466720395262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9079 = 277466720395262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9079 = (17079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9079
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9080) ≤ val WuPaper.ClassicalFourthData.Bq 9080
    have hp : val WuPaper.ClassicalFourthData.Bq 9080 = (277468380545608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9080 = 277468380545608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9080 = (427:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9081) ≤ val WuPaper.ClassicalFourthData.Bq 9081
    have hp : val WuPaper.ClassicalFourthData.Bq 9081 = (277470039132795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9081 = 277470039132795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9081 = (17081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9082) ≤ val WuPaper.ClassicalFourthData.Bq 9082
    have hp : val WuPaper.ClassicalFourthData.Bq 9082 = (277471696157309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9082 = 277471696157309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9082 = (8541:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9083) ≤ val WuPaper.ClassicalFourthData.Bq 9083
    have hp : val WuPaper.ClassicalFourthData.Bq 9083 = (277473351619632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9083 = 277473351619632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9083 = (17083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9084) ≤ val WuPaper.ClassicalFourthData.Bq 9084
    have hp : val WuPaper.ClassicalFourthData.Bq 9084 = (277475005520248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9084 = 277475005520248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9084 = (4271:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9085) ≤ val WuPaper.ClassicalFourthData.Bq 9085
    have hp : val WuPaper.ClassicalFourthData.Bq 9085 = (277476657859640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9085 = 277476657859640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9085 = (3417:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9086) ≤ val WuPaper.ClassicalFourthData.Bq 9086
    have hp : val WuPaper.ClassicalFourthData.Bq 9086 = (277478308638291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9086 = 277478308638291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9086 = (8543:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9087) ≤ val WuPaper.ClassicalFourthData.Bq 9087
    have hp : val WuPaper.ClassicalFourthData.Bq 9087 = (277479957856685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9087 = 277479957856685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9087 = (17087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_567
