import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints253
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_253 (j : Fin 16) (hj : 16*253+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*253+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*253+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4048) ≤ val WuPaper.ClassicalFourthData.Bq 4048
    have hp : val WuPaper.ClassicalFourthData.Bq 4048 = (232114625576857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4048 = 232114625576857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4048 = (753:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4049) ≤ val WuPaper.ClassicalFourthData.Bq 4049
    have hp : val WuPaper.ClassicalFourthData.Bq 4049 = (232136608512477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4049 = 232136608512477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4049 = (12049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4050) ≤ val WuPaper.ClassicalFourthData.Bq 4050
    have hp : val WuPaper.ClassicalFourthData.Bq 4050 = (232158582675712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4050 = 232158582675712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4050 = (241:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4051) ≤ val WuPaper.ClassicalFourthData.Bq 4051
    have hp : val WuPaper.ClassicalFourthData.Bq 4051 = (232180548070021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4051 = 232180548070021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4051 = (12051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4052) ≤ val WuPaper.ClassicalFourthData.Bq 4052
    have hp : val WuPaper.ClassicalFourthData.Bq 4052 = (232202504698857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4052 = 232202504698857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4052 = (3013:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4053) ≤ val WuPaper.ClassicalFourthData.Bq 4053
    have hp : val WuPaper.ClassicalFourthData.Bq 4053 = (232224452565675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4053 = 232224452565675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4053 = (12053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4054) ≤ val WuPaper.ClassicalFourthData.Bq 4054
    have hp : val WuPaper.ClassicalFourthData.Bq 4054 = (232246391673925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4054 = 232246391673925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4054 = (6027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4055) ≤ val WuPaper.ClassicalFourthData.Bq 4055
    have hp : val WuPaper.ClassicalFourthData.Bq 4055 = (232268322027059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4055 = 232268322027059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4055 = (2411:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4055
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4056) ≤ val WuPaper.ClassicalFourthData.Bq 4056
    have hp : val WuPaper.ClassicalFourthData.Bq 4056 = (232290243628524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4056 = 232290243628524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4056 = (1507:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4057) ≤ val WuPaper.ClassicalFourthData.Bq 4057
    have hp : val WuPaper.ClassicalFourthData.Bq 4057 = (232312156481768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4057 = 232312156481768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4057 = (12057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4058) ≤ val WuPaper.ClassicalFourthData.Bq 4058
    have hp : val WuPaper.ClassicalFourthData.Bq 4058 = (232334060590236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4058 = 232334060590236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4058 = (6029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4059) ≤ val WuPaper.ClassicalFourthData.Bq 4059
    have hp : val WuPaper.ClassicalFourthData.Bq 4059 = (232355955957371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4059 = 232355955957371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4059 = (12059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4060) ≤ val WuPaper.ClassicalFourthData.Bq 4060
    have hp : val WuPaper.ClassicalFourthData.Bq 4060 = (232377842586616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4060 = 232377842586616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4060 = (603:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4061) ≤ val WuPaper.ClassicalFourthData.Bq 4061
    have hp : val WuPaper.ClassicalFourthData.Bq 4061 = (232399720481411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4061 = 232399720481411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4061 = (12061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4062) ≤ val WuPaper.ClassicalFourthData.Bq 4062
    have hp : val WuPaper.ClassicalFourthData.Bq 4062 = (232421589645195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4062 = 232421589645195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4062 = (6031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4063) ≤ val WuPaper.ClassicalFourthData.Bq 4063
    have hp : val WuPaper.ClassicalFourthData.Bq 4063 = (232443450081405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4063 = 232443450081405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4063 = (12063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_253
