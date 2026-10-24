import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints064
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_064 (j : Fin 16) (hj : 16*64+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*64+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*64+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1024) ≤ val WuPaper.ClassicalFourthData.Bq 1024
    have hp : val WuPaper.ClassicalFourthData.Bq 1024 = (101033718105500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1024 = 101033718105500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1024 = (282:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1025) ≤ val WuPaper.ClassicalFourthData.Bq 1025
    have hp : val WuPaper.ClassicalFourthData.Bq 1025 = (101110733662161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1025 = 101110733662161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1025 = (361:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1026) ≤ val WuPaper.ClassicalFourthData.Bq 1026
    have hp : val WuPaper.ClassicalFourthData.Bq 1026 = (101187714602930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1026 = 101187714602930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1026 = (4513:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1027) ≤ val WuPaper.ClassicalFourthData.Bq 1027
    have hp : val WuPaper.ClassicalFourthData.Bq 1027 = (101264660946294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1027 = 101264660946294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1027 = (9027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1028) ≤ val WuPaper.ClassicalFourthData.Bq 1028
    have hp : val WuPaper.ClassicalFourthData.Bq 1028 = (101341572710727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1028 = 101341572710727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1028 = (2257:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1029) ≤ val WuPaper.ClassicalFourthData.Bq 1029
    have hp : val WuPaper.ClassicalFourthData.Bq 1029 = (101418449914692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1029 = 101418449914692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1029 = (9029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1030) ≤ val WuPaper.ClassicalFourthData.Bq 1030
    have hp : val WuPaper.ClassicalFourthData.Bq 1030 = (101495292576637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1030 = 101495292576637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1030 = (903:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1031) ≤ val WuPaper.ClassicalFourthData.Bq 1031
    have hp : val WuPaper.ClassicalFourthData.Bq 1031 = (101572100715000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1031 = 101572100715000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1031 = (9031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1031
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1032) ≤ val WuPaper.ClassicalFourthData.Bq 1032
    have hp : val WuPaper.ClassicalFourthData.Bq 1032 = (101648874348206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1032 = 101648874348206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1032 = (1129:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1033) ≤ val WuPaper.ClassicalFourthData.Bq 1033
    have hp : val WuPaper.ClassicalFourthData.Bq 1033 = (101725613494668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1033 = 101725613494668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1033 = (9033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1034) ≤ val WuPaper.ClassicalFourthData.Bq 1034
    have hp : val WuPaper.ClassicalFourthData.Bq 1034 = (101802318172785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1034 = 101802318172785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1034 = (4517:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1035) ≤ val WuPaper.ClassicalFourthData.Bq 1035
    have hp : val WuPaper.ClassicalFourthData.Bq 1035 = (101878988400946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1035 = 101878988400946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1035 = (1807:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1036) ≤ val WuPaper.ClassicalFourthData.Bq 1036
    have hp : val WuPaper.ClassicalFourthData.Bq 1036 = (101955624197526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1036 = 101955624197526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1036 = (2259:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1037) ≤ val WuPaper.ClassicalFourthData.Bq 1037
    have hp : val WuPaper.ClassicalFourthData.Bq 1037 = (102032225580889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1037 = 102032225580889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1037 = (9037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1038) ≤ val WuPaper.ClassicalFourthData.Bq 1038
    have hp : val WuPaper.ClassicalFourthData.Bq 1038 = (102108792569387:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1038 = 102108792569387 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1038 = (4519:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1039) ≤ val WuPaper.ClassicalFourthData.Bq 1039
    have hp : val WuPaper.ClassicalFourthData.Bq 1039 = (102185325181357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1039 = 102185325181357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1039 = (9039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1039
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_064
