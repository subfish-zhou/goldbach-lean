import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints313
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_313 (j : Fin 16) (hj : 16*313+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*313+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*313+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5008) ≤ val WuPaper.ClassicalFourthData.Bq 5008
    have hp : val WuPaper.ClassicalFourthData.Bq 5008 = (249636749777812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5008 = 249636749777812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5008 = (813:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5009) ≤ val WuPaper.ClassicalFourthData.Bq 5009
    have hp : val WuPaper.ClassicalFourthData.Bq 5009 = (249651692382017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5009 = 249651692382017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5009 = (13009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5010) ≤ val WuPaper.ClassicalFourthData.Bq 5010
    have hp : val WuPaper.ClassicalFourthData.Bq 5010 = (249666628900956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5010 = 249666628900956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5010 = (1301:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5011) ≤ val WuPaper.ClassicalFourthData.Bq 5011
    have hp : val WuPaper.ClassicalFourthData.Bq 5011 = (249681559336872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5011 = 249681559336872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5011 = (13011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5012) ≤ val WuPaper.ClassicalFourthData.Bq 5012
    have hp : val WuPaper.ClassicalFourthData.Bq 5012 = (249696483692010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5012 = 249696483692010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5012 = (3253:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5013) ≤ val WuPaper.ClassicalFourthData.Bq 5013
    have hp : val WuPaper.ClassicalFourthData.Bq 5013 = (249711401968611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5013 = 249711401968611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5013 = (13013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5014) ≤ val WuPaper.ClassicalFourthData.Bq 5014
    have hp : val WuPaper.ClassicalFourthData.Bq 5014 = (249726314168916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5014 = 249726314168916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5014 = (6507:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5015) ≤ val WuPaper.ClassicalFourthData.Bq 5015
    have hp : val WuPaper.ClassicalFourthData.Bq 5015 = (249741220295165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5015 = 249741220295165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5015 = (2603:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5015
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5016) ≤ val WuPaper.ClassicalFourthData.Bq 5016
    have hp : val WuPaper.ClassicalFourthData.Bq 5016 = (249756120349596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5016 = 249756120349596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5016 = (1627:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5017) ≤ val WuPaper.ClassicalFourthData.Bq 5017
    have hp : val WuPaper.ClassicalFourthData.Bq 5017 = (249771014334449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5017 = 249771014334449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5017 = (13017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5018) ≤ val WuPaper.ClassicalFourthData.Bq 5018
    have hp : val WuPaper.ClassicalFourthData.Bq 5018 = (249785902251960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5018 = 249785902251960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5018 = (6509:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5019) ≤ val WuPaper.ClassicalFourthData.Bq 5019
    have hp : val WuPaper.ClassicalFourthData.Bq 5019 = (249800784104365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5019 = 249800784104365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5019 = (13019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5020) ≤ val WuPaper.ClassicalFourthData.Bq 5020
    have hp : val WuPaper.ClassicalFourthData.Bq 5020 = (249815659893900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5020 = 249815659893900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5020 = (651:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5021) ≤ val WuPaper.ClassicalFourthData.Bq 5021
    have hp : val WuPaper.ClassicalFourthData.Bq 5021 = (249830529622798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5021 = 249830529622798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5021 = (13021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5022) ≤ val WuPaper.ClassicalFourthData.Bq 5022
    have hp : val WuPaper.ClassicalFourthData.Bq 5022 = (249845393293293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5022 = 249845393293293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5022 = (6511:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5023) ≤ val WuPaper.ClassicalFourthData.Bq 5023
    have hp : val WuPaper.ClassicalFourthData.Bq 5023 = (249860250907617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5023 = 249860250907617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5023 = (13023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_313
