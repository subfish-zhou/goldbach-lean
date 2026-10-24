import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints626
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_626 (j : Fin 16) (hj : 16*626+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*626+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*626+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10016) ≤ val WuPaper.ClassicalFourthData.Bq 10016
    have hp : val WuPaper.ClassicalFourthData.Bq 10016 = (278398129034585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10016 = 278398129034585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10016 = (563:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10017) ≤ val WuPaper.ClassicalFourthData.Bq 10017
    have hp : val WuPaper.ClassicalFourthData.Bq 10017 = (278398516436434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10017 = 278398516436434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10017 = (18017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10018) ≤ val WuPaper.ClassicalFourthData.Bq 10018
    have hp : val WuPaper.ClassicalFourthData.Bq 10018 = (278398902665373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10018 = 278398902665373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10018 = (9009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10019) ≤ val WuPaper.ClassicalFourthData.Bq 10019
    have hp : val WuPaper.ClassicalFourthData.Bq 10019 = (278399287721758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10019 = 278399287721758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10019 = (18019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10020) ≤ val WuPaper.ClassicalFourthData.Bq 10020
    have hp : val WuPaper.ClassicalFourthData.Bq 10020 = (278399671605946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10020 = 278399671605946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10020 = (901:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10021) ≤ val WuPaper.ClassicalFourthData.Bq 10021
    have hp : val WuPaper.ClassicalFourthData.Bq 10021 = (278400054318293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10021 = 278400054318293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10021 = (18021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10022) ≤ val WuPaper.ClassicalFourthData.Bq 10022
    have hp : val WuPaper.ClassicalFourthData.Bq 10022 = (278400435859155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10022 = 278400435859155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10022 = (9011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10023) ≤ val WuPaper.ClassicalFourthData.Bq 10023
    have hp : val WuPaper.ClassicalFourthData.Bq 10023 = (278400816228889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10023 = 278400816228889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10023 = (18023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10023
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10024) ≤ val WuPaper.ClassicalFourthData.Bq 10024
    have hp : val WuPaper.ClassicalFourthData.Bq 10024 = (278401195427849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10024 = 278401195427849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10024 = (2253:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10025) ≤ val WuPaper.ClassicalFourthData.Bq 10025
    have hp : val WuPaper.ClassicalFourthData.Bq 10025 = (278401573456393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10025 = 278401573456393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10025 = (721:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10026) ≤ val WuPaper.ClassicalFourthData.Bq 10026
    have hp : val WuPaper.ClassicalFourthData.Bq 10026 = (278401950314875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10026 = 278401950314875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10026 = (9013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10027) ≤ val WuPaper.ClassicalFourthData.Bq 10027
    have hp : val WuPaper.ClassicalFourthData.Bq 10027 = (278402326003651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10027 = 278402326003651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10027 = (18027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10028) ≤ val WuPaper.ClassicalFourthData.Bq 10028
    have hp : val WuPaper.ClassicalFourthData.Bq 10028 = (278402700523076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10028 = 278402700523076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10028 = (4507:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10029) ≤ val WuPaper.ClassicalFourthData.Bq 10029
    have hp : val WuPaper.ClassicalFourthData.Bq 10029 = (278403073873507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10029 = 278403073873507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10029 = (18029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10030) ≤ val WuPaper.ClassicalFourthData.Bq 10030
    have hp : val WuPaper.ClassicalFourthData.Bq 10030 = (278403446055297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10030 = 278403446055297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10030 = (1803:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10031) ≤ val WuPaper.ClassicalFourthData.Bq 10031
    have hp : val WuPaper.ClassicalFourthData.Bq 10031 = (278403817068803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10031 = 278403817068803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10031 = (18031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_626
