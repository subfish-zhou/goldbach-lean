import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints195
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_195 (j : Fin 16) (hj : 16*195+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*195+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*195+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3120) ≤ val WuPaper.ClassicalFourthData.Bq 3120
    have hp : val WuPaper.ClassicalFourthData.Bq 3120 = (207414879246041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3120 = 207414879246041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3120 = (139:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3121) ≤ val WuPaper.ClassicalFourthData.Bq 3121
    have hp : val WuPaper.ClassicalFourthData.Bq 3121 = (207446741796636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3121 = 207446741796636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3121 = (11121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3122) ≤ val WuPaper.ClassicalFourthData.Bq 3122
    have hp : val WuPaper.ClassicalFourthData.Bq 3122 = (207478591525156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3122 = 207478591525156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3122 = (5561:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3123) ≤ val WuPaper.ClassicalFourthData.Bq 3123
    have hp : val WuPaper.ClassicalFourthData.Bq 3123 = (207510428437050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3123 = 207510428437050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3123 = (11123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3124) ≤ val WuPaper.ClassicalFourthData.Bq 3124
    have hp : val WuPaper.ClassicalFourthData.Bq 3124 = (207542252537766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3124 = 207542252537766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3124 = (2781:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3125) ≤ val WuPaper.ClassicalFourthData.Bq 3125
    have hp : val WuPaper.ClassicalFourthData.Bq 3125 = (207574063832746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3125 = 207574063832746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3125 = (89:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3126) ≤ val WuPaper.ClassicalFourthData.Bq 3126
    have hp : val WuPaper.ClassicalFourthData.Bq 3126 = (207605862327433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3126 = 207605862327433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3126 = (5563:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3127) ≤ val WuPaper.ClassicalFourthData.Bq 3127
    have hp : val WuPaper.ClassicalFourthData.Bq 3127 = (207637648027265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3127 = 207637648027265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3127 = (11127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3127
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3128) ≤ val WuPaper.ClassicalFourthData.Bq 3128
    have hp : val WuPaper.ClassicalFourthData.Bq 3128 = (207669420937678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3128 = 207669420937678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3128 = (1391:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3129) ≤ val WuPaper.ClassicalFourthData.Bq 3129
    have hp : val WuPaper.ClassicalFourthData.Bq 3129 = (207701181064104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3129 = 207701181064104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3129 = (11129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3130) ≤ val WuPaper.ClassicalFourthData.Bq 3130
    have hp : val WuPaper.ClassicalFourthData.Bq 3130 = (207732928411973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3130 = 207732928411973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3130 = (1113:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3131) ≤ val WuPaper.ClassicalFourthData.Bq 3131
    have hp : val WuPaper.ClassicalFourthData.Bq 3131 = (207764662986714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3131 = 207764662986714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3131 = (11131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3132) ≤ val WuPaper.ClassicalFourthData.Bq 3132
    have hp : val WuPaper.ClassicalFourthData.Bq 3132 = (207796384793749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3132 = 207796384793749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3132 = (2783:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3133) ≤ val WuPaper.ClassicalFourthData.Bq 3133
    have hp : val WuPaper.ClassicalFourthData.Bq 3133 = (207828093838502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3133 = 207828093838502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3133 = (11133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3134) ≤ val WuPaper.ClassicalFourthData.Bq 3134
    have hp : val WuPaper.ClassicalFourthData.Bq 3134 = (207859790126391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3134 = 207859790126391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3134 = (5567:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3135) ≤ val WuPaper.ClassicalFourthData.Bq 3135
    have hp : val WuPaper.ClassicalFourthData.Bq 3135 = (207891473662833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3135 = 207891473662833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3135 = (2227:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_195
