import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints194
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_194 (j : Fin 16) (hj : 16*194+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*194+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*194+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3104) ≤ val WuPaper.ClassicalFourthData.Bq 3104
    have hp : val WuPaper.ClassicalFourthData.Bq 3104 = (206903330176506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3104 = 206903330176506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3104 = (347:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3105) ≤ val WuPaper.ClassicalFourthData.Bq 3105
    have hp : val WuPaper.ClassicalFourthData.Bq 3105 = (206935398623746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3105 = 206935398623746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3105 = (2221:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3106) ≤ val WuPaper.ClassicalFourthData.Bq 3106
    have hp : val WuPaper.ClassicalFourthData.Bq 3106 = (206967454161335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3106 = 206967454161335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3106 = (5553:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3107) ≤ val WuPaper.ClassicalFourthData.Bq 3107
    have hp : val WuPaper.ClassicalFourthData.Bq 3107 = (206999496794767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3107 = 206999496794767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3107 = (11107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3108) ≤ val WuPaper.ClassicalFourthData.Bq 3108
    have hp : val WuPaper.ClassicalFourthData.Bq 3108 = (207031526529534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3108 = 207031526529534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3108 = (2777:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3109) ≤ val WuPaper.ClassicalFourthData.Bq 3109
    have hp : val WuPaper.ClassicalFourthData.Bq 3109 = (207063543371125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3109 = 207063543371125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3109 = (11109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3110) ≤ val WuPaper.ClassicalFourthData.Bq 3110
    have hp : val WuPaper.ClassicalFourthData.Bq 3110 = (207095547325026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3110 = 207095547325026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3110 = (1111:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3111) ≤ val WuPaper.ClassicalFourthData.Bq 3111
    have hp : val WuPaper.ClassicalFourthData.Bq 3111 = (207127538396721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3111 = 207127538396721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3111 = (11111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3111
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3112) ≤ val WuPaper.ClassicalFourthData.Bq 3112
    have hp : val WuPaper.ClassicalFourthData.Bq 3112 = (207159516591690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3112 = 207159516591690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3112 = (1389:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3113) ≤ val WuPaper.ClassicalFourthData.Bq 3113
    have hp : val WuPaper.ClassicalFourthData.Bq 3113 = (207191481915410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3113 = 207191481915410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3113 = (11113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3114) ≤ val WuPaper.ClassicalFourthData.Bq 3114
    have hp : val WuPaper.ClassicalFourthData.Bq 3114 = (207223434373358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3114 = 207223434373358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3114 = (5557:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3115) ≤ val WuPaper.ClassicalFourthData.Bq 3115
    have hp : val WuPaper.ClassicalFourthData.Bq 3115 = (207255373971004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3115 = 207255373971004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3115 = (2223:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3116) ≤ val WuPaper.ClassicalFourthData.Bq 3116
    have hp : val WuPaper.ClassicalFourthData.Bq 3116 = (207287300713818:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3116 = 207287300713818 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3116 = (2779:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3117) ≤ val WuPaper.ClassicalFourthData.Bq 3117
    have hp : val WuPaper.ClassicalFourthData.Bq 3117 = (207319214607266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3117 = 207319214607266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3117 = (11117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3118) ≤ val WuPaper.ClassicalFourthData.Bq 3118
    have hp : val WuPaper.ClassicalFourthData.Bq 3118 = (207351115656813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3118 = 207351115656813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3118 = (5559:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3119) ≤ val WuPaper.ClassicalFourthData.Bq 3119
    have hp : val WuPaper.ClassicalFourthData.Bq 3119 = (207383003867919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3119 = 207383003867919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3119 = (11119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_194
