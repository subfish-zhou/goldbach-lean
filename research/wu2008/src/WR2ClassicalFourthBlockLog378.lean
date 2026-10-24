import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints378
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_378 (j : Fin 16) (hj : 16*378+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*378+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*378+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6048) ≤ val WuPaper.ClassicalFourthData.Bq 6048
    have hp : val WuPaper.ClassicalFourthData.Bq 6048 = (262266300855915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6048 = 262266300855915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6048 = (439:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6049) ≤ val WuPaper.ClassicalFourthData.Bq 6049
    have hp : val WuPaper.ClassicalFourthData.Bq 6049 = (262275967242352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6049 = 262275967242352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6049 = (14049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6050) ≤ val WuPaper.ClassicalFourthData.Bq 6050
    have hp : val WuPaper.ClassicalFourthData.Bq 6050 = (262285629433513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6050 = 262285629433513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6050 = (281:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6051) ≤ val WuPaper.ClassicalFourthData.Bq 6051
    have hp : val WuPaper.ClassicalFourthData.Bq 6051 = (262295287430854:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6051 = 262295287430854 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6051 = (14051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6052) ≤ val WuPaper.ClassicalFourthData.Bq 6052
    have hp : val WuPaper.ClassicalFourthData.Bq 6052 = (262304941235831:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6052 = 262304941235831 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6052 = (3513:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6053) ≤ val WuPaper.ClassicalFourthData.Bq 6053
    have hp : val WuPaper.ClassicalFourthData.Bq 6053 = (262314590849901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6053 = 262314590849901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6053 = (14053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6054) ≤ val WuPaper.ClassicalFourthData.Bq 6054
    have hp : val WuPaper.ClassicalFourthData.Bq 6054 = (262324236274517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6054 = 262324236274517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6054 = (7027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6055) ≤ val WuPaper.ClassicalFourthData.Bq 6055
    have hp : val WuPaper.ClassicalFourthData.Bq 6055 = (262333877511134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6055 = 262333877511134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6055 = (2811:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6055
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6056) ≤ val WuPaper.ClassicalFourthData.Bq 6056
    have hp : val WuPaper.ClassicalFourthData.Bq 6056 = (262343514561206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6056 = 262343514561206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6056 = (1757:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6057) ≤ val WuPaper.ClassicalFourthData.Bq 6057
    have hp : val WuPaper.ClassicalFourthData.Bq 6057 = (262353147426186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6057 = 262353147426186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6057 = (14057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6058) ≤ val WuPaper.ClassicalFourthData.Bq 6058
    have hp : val WuPaper.ClassicalFourthData.Bq 6058 = (262362776107527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6058 = 262362776107527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6058 = (7029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6059) ≤ val WuPaper.ClassicalFourthData.Bq 6059
    have hp : val WuPaper.ClassicalFourthData.Bq 6059 = (262372400606681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6059 = 262372400606681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6059 = (14059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6060) ≤ val WuPaper.ClassicalFourthData.Bq 6060
    have hp : val WuPaper.ClassicalFourthData.Bq 6060 = (262382020925099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6060 = 262382020925099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6060 = (703:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6061) ≤ val WuPaper.ClassicalFourthData.Bq 6061
    have hp : val WuPaper.ClassicalFourthData.Bq 6061 = (262391637064233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6061 = 262391637064233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6061 = (14061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6062) ≤ val WuPaper.ClassicalFourthData.Bq 6062
    have hp : val WuPaper.ClassicalFourthData.Bq 6062 = (262401249025532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6062 = 262401249025532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6062 = (7031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6063) ≤ val WuPaper.ClassicalFourthData.Bq 6063
    have hp : val WuPaper.ClassicalFourthData.Bq 6063 = (262410856810446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6063 = 262410856810446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6063 = (14063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_378
