import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints063
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_063 (j : Fin 16) (hj : 16*63+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*63+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*63+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1008) ≤ val WuPaper.ClassicalFourthData.Bq 1008
    have hp : val WuPaper.ClassicalFourthData.Bq 1008 = (99796746304577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1008 = 99796746304577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1008 = (563:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1009) ≤ val WuPaper.ClassicalFourthData.Bq 1009
    have hp : val WuPaper.ClassicalFourthData.Bq 1009 = (99874318239800:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1009 = 99874318239800 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1009 = (9009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1010) ≤ val WuPaper.ClassicalFourthData.Bq 1010
    have hp : val WuPaper.ClassicalFourthData.Bq 1010 = (99951855261658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1010 = 99951855261658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1010 = (901:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1011) ≤ val WuPaper.ClassicalFourthData.Bq 1011
    have hp : val WuPaper.ClassicalFourthData.Bq 1011 = (100029357388835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1011 = 100029357388835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1011 = (9011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1012) ≤ val WuPaper.ClassicalFourthData.Bq 1012
    have hp : val WuPaper.ClassicalFourthData.Bq 1012 = (100106824640005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1012 = 100106824640005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1012 = (2253:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1013) ≤ val WuPaper.ClassicalFourthData.Bq 1013
    have hp : val WuPaper.ClassicalFourthData.Bq 1013 = (100184257033830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1013 = 100184257033830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1013 = (9013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1014) ≤ val WuPaper.ClassicalFourthData.Bq 1014
    have hp : val WuPaper.ClassicalFourthData.Bq 1014 = (100261654588956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1014 = 100261654588956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1014 = (4507:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1015) ≤ val WuPaper.ClassicalFourthData.Bq 1015
    have hp : val WuPaper.ClassicalFourthData.Bq 1015 = (100339017324020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1015 = 100339017324020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1015 = (1803:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1015
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1016) ≤ val WuPaper.ClassicalFourthData.Bq 1016
    have hp : val WuPaper.ClassicalFourthData.Bq 1016 = (100416345257644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1016 = 100416345257644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1016 = (1127:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1017) ≤ val WuPaper.ClassicalFourthData.Bq 1017
    have hp : val WuPaper.ClassicalFourthData.Bq 1017 = (100493638408440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1017 = 100493638408440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1017 = (9017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1018) ≤ val WuPaper.ClassicalFourthData.Bq 1018
    have hp : val WuPaper.ClassicalFourthData.Bq 1018 = (100570896795006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1018 = 100570896795006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1018 = (4509:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1019) ≤ val WuPaper.ClassicalFourthData.Bq 1019
    have hp : val WuPaper.ClassicalFourthData.Bq 1019 = (100648120435927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1019 = 100648120435927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1019 = (9019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1020) ≤ val WuPaper.ClassicalFourthData.Bq 1020
    have hp : val WuPaper.ClassicalFourthData.Bq 1020 = (100725309349778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1020 = 100725309349778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1020 = (451:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1021) ≤ val WuPaper.ClassicalFourthData.Bq 1021
    have hp : val WuPaper.ClassicalFourthData.Bq 1021 = (100802463555118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1021 = 100802463555118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1021 = (9021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1022) ≤ val WuPaper.ClassicalFourthData.Bq 1022
    have hp : val WuPaper.ClassicalFourthData.Bq 1022 = (100879583070496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1022 = 100879583070496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1022 = (4511:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1023) ≤ val WuPaper.ClassicalFourthData.Bq 1023
    have hp : val WuPaper.ClassicalFourthData.Bq 1023 = (100956667914449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1023 = 100956667914449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1023 = (9023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_063
