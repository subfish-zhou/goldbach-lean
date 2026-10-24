import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints566
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_566 (j : Fin 16) (hj : 16*566+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*566+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*566+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9056) ≤ val WuPaper.ClassicalFourthData.Bq 9056
    have hp : val WuPaper.ClassicalFourthData.Bq 9056 = (277428104390615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9056 = 277428104390615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9056 = (533:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9057) ≤ val WuPaper.ClassicalFourthData.Bq 9057
    have hp : val WuPaper.ClassicalFourthData.Bq 9057 = (277429800627489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9057 = 277429800627489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9057 = (17057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9058) ≤ val WuPaper.ClassicalFourthData.Bq 9058
    have hp : val WuPaper.ClassicalFourthData.Bq 9058 = (277431495290033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9058 = 277431495290033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9058 = (8529:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9059) ≤ val WuPaper.ClassicalFourthData.Bq 9059
    have hp : val WuPaper.ClassicalFourthData.Bq 9059 = (277433188378734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9059 = 277433188378734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9059 = (17059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9060) ≤ val WuPaper.ClassicalFourthData.Bq 9060
    have hp : val WuPaper.ClassicalFourthData.Bq 9060 = (277434879894082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9060 = 277434879894082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9060 = (853:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9061) ≤ val WuPaper.ClassicalFourthData.Bq 9061
    have hp : val WuPaper.ClassicalFourthData.Bq 9061 = (277436569836561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9061 = 277436569836561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9061 = (17061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9062) ≤ val WuPaper.ClassicalFourthData.Bq 9062
    have hp : val WuPaper.ClassicalFourthData.Bq 9062 = (277438258206660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9062 = 277438258206660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9062 = (8531:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9063) ≤ val WuPaper.ClassicalFourthData.Bq 9063
    have hp : val WuPaper.ClassicalFourthData.Bq 9063 = (277439945004866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9063 = 277439945004866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9063 = (17063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9063
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9064) ≤ val WuPaper.ClassicalFourthData.Bq 9064
    have hp : val WuPaper.ClassicalFourthData.Bq 9064 = (277441630231664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9064 = 277441630231664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9064 = (2133:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9065) ≤ val WuPaper.ClassicalFourthData.Bq 9065
    have hp : val WuPaper.ClassicalFourthData.Bq 9065 = (277443313887542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9065 = 277443313887542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9065 = (3413:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9066) ≤ val WuPaper.ClassicalFourthData.Bq 9066
    have hp : val WuPaper.ClassicalFourthData.Bq 9066 = (277444995972986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9066 = 277444995972986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9066 = (8533:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9067) ≤ val WuPaper.ClassicalFourthData.Bq 9067
    have hp : val WuPaper.ClassicalFourthData.Bq 9067 = (277446676488482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9067 = 277446676488482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9067 = (17067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9068) ≤ val WuPaper.ClassicalFourthData.Bq 9068
    have hp : val WuPaper.ClassicalFourthData.Bq 9068 = (277448355434516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9068 = 277448355434516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9068 = (4267:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9069) ≤ val WuPaper.ClassicalFourthData.Bq 9069
    have hp : val WuPaper.ClassicalFourthData.Bq 9069 = (277450032811575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9069 = 277450032811575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9069 = (17069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9070) ≤ val WuPaper.ClassicalFourthData.Bq 9070
    have hp : val WuPaper.ClassicalFourthData.Bq 9070 = (277451708620143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9070 = 277451708620143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9070 = (1707:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9071) ≤ val WuPaper.ClassicalFourthData.Bq 9071
    have hp : val WuPaper.ClassicalFourthData.Bq 9071 = (277453382860707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9071 = 277453382860707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9071 = (17071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_566
