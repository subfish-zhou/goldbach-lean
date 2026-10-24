import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints188
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_188 (j : Fin 16) (hj : 16*188+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*188+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*188+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3008) ≤ val WuPaper.ClassicalFourthData.Bq 3008
    have hp : val WuPaper.ClassicalFourthData.Bq 3008 = (203763805419404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3008 = 203763805419404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3008 = (344:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3009) ≤ val WuPaper.ClassicalFourthData.Bq 3009
    have hp : val WuPaper.ClassicalFourthData.Bq 3009 = (203797139212753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3009 = 203797139212753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3009 = (11009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3010) ≤ val WuPaper.ClassicalFourthData.Bq 3010
    have hp : val WuPaper.ClassicalFourthData.Bq 3010 = (203830459555535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3010 = 203830459555535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3010 = (1101:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3011) ≤ val WuPaper.ClassicalFourthData.Bq 3011
    have hp : val WuPaper.ClassicalFourthData.Bq 3011 = (203863766453525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3011 = 203863766453525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3011 = (11011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3012) ≤ val WuPaper.ClassicalFourthData.Bq 3012
    have hp : val WuPaper.ClassicalFourthData.Bq 3012 = (203897059912495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3012 = 203897059912495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3012 = (2753:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3013) ≤ val WuPaper.ClassicalFourthData.Bq 3013
    have hp : val WuPaper.ClassicalFourthData.Bq 3013 = (203930339938213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3013 = 203930339938213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3013 = (11013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3014) ≤ val WuPaper.ClassicalFourthData.Bq 3014
    have hp : val WuPaper.ClassicalFourthData.Bq 3014 = (203963606536443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3014 = 203963606536443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3014 = (5507:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3015) ≤ val WuPaper.ClassicalFourthData.Bq 3015
    have hp : val WuPaper.ClassicalFourthData.Bq 3015 = (203996859712950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3015 = 203996859712950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3015 = (2203:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3015
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3016) ≤ val WuPaper.ClassicalFourthData.Bq 3016
    have hp : val WuPaper.ClassicalFourthData.Bq 3016 = (204030099473490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3016 = 204030099473490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3016 = (1377:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3017) ≤ val WuPaper.ClassicalFourthData.Bq 3017
    have hp : val WuPaper.ClassicalFourthData.Bq 3017 = (204063325823822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3017 = 204063325823822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3017 = (11017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3018) ≤ val WuPaper.ClassicalFourthData.Bq 3018
    have hp : val WuPaper.ClassicalFourthData.Bq 3018 = (204096538769698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3018 = 204096538769698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3018 = (5509:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3019) ≤ val WuPaper.ClassicalFourthData.Bq 3019
    have hp : val WuPaper.ClassicalFourthData.Bq 3019 = (204129738316869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3019 = 204129738316869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3019 = (11019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3020) ≤ val WuPaper.ClassicalFourthData.Bq 3020
    have hp : val WuPaper.ClassicalFourthData.Bq 3020 = (204162924471082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3020 = 204162924471082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3020 = (551:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3021) ≤ val WuPaper.ClassicalFourthData.Bq 3021
    have hp : val WuPaper.ClassicalFourthData.Bq 3021 = (204196097238081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3021 = 204196097238081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3021 = (11021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3022) ≤ val WuPaper.ClassicalFourthData.Bq 3022
    have hp : val WuPaper.ClassicalFourthData.Bq 3022 = (204229256623608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3022 = 204229256623608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3022 = (5511:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3023) ≤ val WuPaper.ClassicalFourthData.Bq 3023
    have hp : val WuPaper.ClassicalFourthData.Bq 3023 = (204262402633401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3023 = 204262402633401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3023 = (11023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_188
