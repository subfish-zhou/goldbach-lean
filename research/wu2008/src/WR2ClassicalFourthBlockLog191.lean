import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints191
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_191 (j : Fin 16) (hj : 16*191+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*191+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*191+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3056) ≤ val WuPaper.ClassicalFourthData.Bq 3056
    have hp : val WuPaper.ClassicalFourthData.Bq 3056 = (205348754553039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3056 = 205348754553039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3056 = (691:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3057) ≤ val WuPaper.ClassicalFourthData.Bq 3057
    have hp : val WuPaper.ClassicalFourthData.Bq 3057 = (205381449181081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3057 = 205381449181081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3057 = (11057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3058) ≤ val WuPaper.ClassicalFourthData.Bq 3058
    have hp : val WuPaper.ClassicalFourthData.Bq 3058 = (205414130632371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3058 = 205414130632371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3058 = (5529:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3059) ≤ val WuPaper.ClassicalFourthData.Bq 3059
    have hp : val WuPaper.ClassicalFourthData.Bq 3059 = (205446798912540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3059 = 205446798912540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3059 = (11059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3060) ≤ val WuPaper.ClassicalFourthData.Bq 3060
    have hp : val WuPaper.ClassicalFourthData.Bq 3060 = (205479454027219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3060 = 205479454027219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3060 = (553:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3061) ≤ val WuPaper.ClassicalFourthData.Bq 3061
    have hp : val WuPaper.ClassicalFourthData.Bq 3061 = (205512095982034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3061 = 205512095982034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3061 = (11061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3062) ≤ val WuPaper.ClassicalFourthData.Bq 3062
    have hp : val WuPaper.ClassicalFourthData.Bq 3062 = (205544724782609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3062 = 205544724782609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3062 = (5531:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3063) ≤ val WuPaper.ClassicalFourthData.Bq 3063
    have hp : val WuPaper.ClassicalFourthData.Bq 3063 = (205577340434564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3063 = 205577340434564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3063 = (11063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3063
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3064) ≤ val WuPaper.ClassicalFourthData.Bq 3064
    have hp : val WuPaper.ClassicalFourthData.Bq 3064 = (205609942943518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3064 = 205609942943518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3064 = (1383:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3065) ≤ val WuPaper.ClassicalFourthData.Bq 3065
    have hp : val WuPaper.ClassicalFourthData.Bq 3065 = (205642532315084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3065 = 205642532315084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3065 = (2213:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3066) ≤ val WuPaper.ClassicalFourthData.Bq 3066
    have hp : val WuPaper.ClassicalFourthData.Bq 3066 = (205675108554876:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3066 = 205675108554876 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3066 = (5533:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3067) ≤ val WuPaper.ClassicalFourthData.Bq 3067
    have hp : val WuPaper.ClassicalFourthData.Bq 3067 = (205707671668502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3067 = 205707671668502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3067 = (11067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3068) ≤ val WuPaper.ClassicalFourthData.Bq 3068
    have hp : val WuPaper.ClassicalFourthData.Bq 3068 = (205740221661569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3068 = 205740221661569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3068 = (2767:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3069) ≤ val WuPaper.ClassicalFourthData.Bq 3069
    have hp : val WuPaper.ClassicalFourthData.Bq 3069 = (205772758539679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3069 = 205772758539679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3069 = (11069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3070) ≤ val WuPaper.ClassicalFourthData.Bq 3070
    have hp : val WuPaper.ClassicalFourthData.Bq 3070 = (205805282308434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3070 = 205805282308434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3070 = (1107:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3071) ≤ val WuPaper.ClassicalFourthData.Bq 3071
    have hp : val WuPaper.ClassicalFourthData.Bq 3071 = (205837792973431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3071 = 205837792973431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3071 = (11071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_191
