import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints317
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_317 (j : Fin 16) (hj : 16*317+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*317+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*317+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5072) ≤ val WuPaper.ClassicalFourthData.Bq 5072
    have hp : val WuPaper.ClassicalFourthData.Bq 5072 = (250580901427634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5072 = 250580901427634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5072 = (817:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5073) ≤ val WuPaper.ClassicalFourthData.Bq 5073
    have hp : val WuPaper.ClassicalFourthData.Bq 5073 = (250595459058396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5073 = 250595459058396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5073 = (13073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5074) ≤ val WuPaper.ClassicalFourthData.Bq 5074
    have hp : val WuPaper.ClassicalFourthData.Bq 5074 = (250610010745566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5074 = 250610010745566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5074 = (6537:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5075) ≤ val WuPaper.ClassicalFourthData.Bq 5075
    have hp : val WuPaper.ClassicalFourthData.Bq 5075 = (250624556491327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5075 = 250624556491327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5075 = (523:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5076) ≤ val WuPaper.ClassicalFourthData.Bq 5076
    have hp : val WuPaper.ClassicalFourthData.Bq 5076 = (250639096297861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5076 = 250639096297861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5076 = (3269:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5077) ≤ val WuPaper.ClassicalFourthData.Bq 5077
    have hp : val WuPaper.ClassicalFourthData.Bq 5077 = (250653630167348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5077 = 250653630167348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5077 = (13077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5078) ≤ val WuPaper.ClassicalFourthData.Bq 5078
    have hp : val WuPaper.ClassicalFourthData.Bq 5078 = (250668158101968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5078 = 250668158101968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5078 = (6539:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5079) ≤ val WuPaper.ClassicalFourthData.Bq 5079
    have hp : val WuPaper.ClassicalFourthData.Bq 5079 = (250682680103901:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5079 = 250682680103901 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5079 = (13079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5079
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5080) ≤ val WuPaper.ClassicalFourthData.Bq 5080
    have hp : val WuPaper.ClassicalFourthData.Bq 5080 = (250697196175325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5080 = 250697196175325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5080 = (327:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5081) ≤ val WuPaper.ClassicalFourthData.Bq 5081
    have hp : val WuPaper.ClassicalFourthData.Bq 5081 = (250711706318417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5081 = 250711706318417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5081 = (13081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5082) ≤ val WuPaper.ClassicalFourthData.Bq 5082
    have hp : val WuPaper.ClassicalFourthData.Bq 5082 = (250726210535353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5082 = 250726210535353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5082 = (6541:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5083) ≤ val WuPaper.ClassicalFourthData.Bq 5083
    have hp : val WuPaper.ClassicalFourthData.Bq 5083 = (250740708828308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5083 = 250740708828308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5083 = (13083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5084) ≤ val WuPaper.ClassicalFourthData.Bq 5084
    have hp : val WuPaper.ClassicalFourthData.Bq 5084 = (250755201199457:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5084 = 250755201199457 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5084 = (3271:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5085) ≤ val WuPaper.ClassicalFourthData.Bq 5085
    have hp : val WuPaper.ClassicalFourthData.Bq 5085 = (250769687650973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5085 = 250769687650973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5085 = (2617:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5086) ≤ val WuPaper.ClassicalFourthData.Bq 5086
    have hp : val WuPaper.ClassicalFourthData.Bq 5086 = (250784168185029:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5086 = 250784168185029 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5086 = (6543:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5087) ≤ val WuPaper.ClassicalFourthData.Bq 5087
    have hp : val WuPaper.ClassicalFourthData.Bq 5087 = (250798642803797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5087 = 250798642803797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5087 = (13087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_317
