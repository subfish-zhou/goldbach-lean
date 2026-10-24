import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints466
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_466 (j : Fin 16) (hj : 16*466+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*466+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*466+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7456) ≤ val WuPaper.ClassicalFourthData.Bq 7456
    have hp : val WuPaper.ClassicalFourthData.Bq 7456 = (272313470263760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7456 = 272313470263760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7456 = (483:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7456
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7457) ≤ val WuPaper.ClassicalFourthData.Bq 7457
    have hp : val WuPaper.ClassicalFourthData.Bq 7457 = (272318441040919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7457 = 272318441040919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7457 = (15457:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7457
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7458) ≤ val WuPaper.ClassicalFourthData.Bq 7458
    have hp : val WuPaper.ClassicalFourthData.Bq 7458 = (272323409203589:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7458 = 272323409203589 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7458 = (7729:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7458
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7459) ≤ val WuPaper.ClassicalFourthData.Bq 7459
    have hp : val WuPaper.ClassicalFourthData.Bq 7459 = (272328374752622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7459 = 272328374752622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7459 = (15459:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7459
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7460) ≤ val WuPaper.ClassicalFourthData.Bq 7460
    have hp : val WuPaper.ClassicalFourthData.Bq 7460 = (272333337688870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7460 = 272333337688870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7460 = (773:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7460
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7461) ≤ val WuPaper.ClassicalFourthData.Bq 7461
    have hp : val WuPaper.ClassicalFourthData.Bq 7461 = (272338298013182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7461 = 272338298013182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7461 = (15461:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7461
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7462) ≤ val WuPaper.ClassicalFourthData.Bq 7462
    have hp : val WuPaper.ClassicalFourthData.Bq 7462 = (272343255726410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7462 = 272343255726410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7462 = (7731:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7462
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7463) ≤ val WuPaper.ClassicalFourthData.Bq 7463
    have hp : val WuPaper.ClassicalFourthData.Bq 7463 = (272348210829403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7463 = 272348210829403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7463 = (15463:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7463
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7464) ≤ val WuPaper.ClassicalFourthData.Bq 7464
    have hp : val WuPaper.ClassicalFourthData.Bq 7464 = (272353163323012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7464 = 272353163323012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7464 = (1933:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7464
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7465) ≤ val WuPaper.ClassicalFourthData.Bq 7465
    have hp : val WuPaper.ClassicalFourthData.Bq 7465 = (272358113208086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7465 = 272358113208086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7465 = (3093:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7465
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7466) ≤ val WuPaper.ClassicalFourthData.Bq 7466
    have hp : val WuPaper.ClassicalFourthData.Bq 7466 = (272363060485475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7466 = 272363060485475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7466 = (7733:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7466
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7467) ≤ val WuPaper.ClassicalFourthData.Bq 7467
    have hp : val WuPaper.ClassicalFourthData.Bq 7467 = (272368005156027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7467 = 272368005156027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7467 = (15467:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7467
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7468) ≤ val WuPaper.ClassicalFourthData.Bq 7468
    have hp : val WuPaper.ClassicalFourthData.Bq 7468 = (272372947220591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7468 = 272372947220591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7468 = (3867:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7468
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7469) ≤ val WuPaper.ClassicalFourthData.Bq 7469
    have hp : val WuPaper.ClassicalFourthData.Bq 7469 = (272377886680015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7469 = 272377886680015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7469 = (15469:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7469
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7470) ≤ val WuPaper.ClassicalFourthData.Bq 7470
    have hp : val WuPaper.ClassicalFourthData.Bq 7470 = (272382823535148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7470 = 272382823535148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7470 = (1547:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7470
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7471) ≤ val WuPaper.ClassicalFourthData.Bq 7471
    have hp : val WuPaper.ClassicalFourthData.Bq 7471 = (272387757786837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7471 = 272387757786837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7471 = (15471:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7471
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_466
