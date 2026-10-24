import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints132
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_132 (j : Fin 16) (hj : 16*132+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*132+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*132+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2112) ≤ val WuPaper.ClassicalFourthData.Bq 2112
    have hp : val WuPaper.ClassicalFourthData.Bq 2112 = (167705573870384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2112 = 167705573870384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2112 = (316:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2113) ≤ val WuPaper.ClassicalFourthData.Bq 2113
    have hp : val WuPaper.ClassicalFourthData.Bq 2113 = (167753699170058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2113 = 167753699170058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2113 = (10113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2114) ≤ val WuPaper.ClassicalFourthData.Bq 2114
    have hp : val WuPaper.ClassicalFourthData.Bq 2114 = (167801804369687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2114 = 167801804369687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2114 = (5057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2115) ≤ val WuPaper.ClassicalFourthData.Bq 2115
    have hp : val WuPaper.ClassicalFourthData.Bq 2115 = (167849889478694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2115 = 167849889478694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2115 = (2023:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2116) ≤ val WuPaper.ClassicalFourthData.Bq 2116
    have hp : val WuPaper.ClassicalFourthData.Bq 2116 = (167897954506495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2116 = 167897954506495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2116 = (2529:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2117) ≤ val WuPaper.ClassicalFourthData.Bq 2117
    have hp : val WuPaper.ClassicalFourthData.Bq 2117 = (167945999462504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2117 = 167945999462504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2117 = (10117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2118) ≤ val WuPaper.ClassicalFourthData.Bq 2118
    have hp : val WuPaper.ClassicalFourthData.Bq 2118 = (167994024356127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2118 = 167994024356127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2118 = (5059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2119) ≤ val WuPaper.ClassicalFourthData.Bq 2119
    have hp : val WuPaper.ClassicalFourthData.Bq 2119 = (168042029196764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2119 = 168042029196764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2119 = (10119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2120) ≤ val WuPaper.ClassicalFourthData.Bq 2120
    have hp : val WuPaper.ClassicalFourthData.Bq 2120 = (168090013993812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2120 = 168090013993812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2120 = (253:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2121) ≤ val WuPaper.ClassicalFourthData.Bq 2121
    have hp : val WuPaper.ClassicalFourthData.Bq 2121 = (168137978756662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2121 = 168137978756662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2121 = (10121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2122) ≤ val WuPaper.ClassicalFourthData.Bq 2122
    have hp : val WuPaper.ClassicalFourthData.Bq 2122 = (168185923494697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2122 = 168185923494697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2122 = (5061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2123) ≤ val WuPaper.ClassicalFourthData.Bq 2123
    have hp : val WuPaper.ClassicalFourthData.Bq 2123 = (168233848217298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2123 = 168233848217298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2123 = (10123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2124) ≤ val WuPaper.ClassicalFourthData.Bq 2124
    have hp : val WuPaper.ClassicalFourthData.Bq 2124 = (168281752933840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2124 = 168281752933840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2124 = (2531:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2125) ≤ val WuPaper.ClassicalFourthData.Bq 2125
    have hp : val WuPaper.ClassicalFourthData.Bq 2125 = (168329637653689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2125 = 168329637653689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2125 = (81:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2126) ≤ val WuPaper.ClassicalFourthData.Bq 2126
    have hp : val WuPaper.ClassicalFourthData.Bq 2126 = (168377502386211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2126 = 168377502386211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2126 = (5063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2127) ≤ val WuPaper.ClassicalFourthData.Bq 2127
    have hp : val WuPaper.ClassicalFourthData.Bq 2127 = (168425347140764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2127 = 168425347140764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2127 = (10127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_132
