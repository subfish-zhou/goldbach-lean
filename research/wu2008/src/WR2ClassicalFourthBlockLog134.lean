import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints134
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_134 (j : Fin 16) (hj : 16*134+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*134+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*134+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2144) ≤ val WuPaper.ClassicalFourthData.Bq 2144
    have hp : val WuPaper.ClassicalFourthData.Bq 2144 = (169235660380710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2144 = 169235660380710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2144 = (317:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2145) ≤ val WuPaper.ClassicalFourthData.Bq 2145
    have hp : val WuPaper.ClassicalFourthData.Bq 2145 = (169283147125918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2145 = 169283147125918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2145 = (2029:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2146) ≤ val WuPaper.ClassicalFourthData.Bq 2146
    have hp : val WuPaper.ClassicalFourthData.Bq 2146 = (169330614069940:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2146 = 169330614069940 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2146 = (5073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2147) ≤ val WuPaper.ClassicalFourthData.Bq 2147
    have hp : val WuPaper.ClassicalFourthData.Bq 2147 = (169378061222029:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2147 = 169378061222029 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2147 = (10147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2148) ≤ val WuPaper.ClassicalFourthData.Bq 2148
    have hp : val WuPaper.ClassicalFourthData.Bq 2148 = (169425488591431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2148 = 169425488591431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2148 = (2537:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2149) ≤ val WuPaper.ClassicalFourthData.Bq 2149
    have hp : val WuPaper.ClassicalFourthData.Bq 2149 = (169472896187385:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2149 = 169472896187385 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2149 = (10149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2150) ≤ val WuPaper.ClassicalFourthData.Bq 2150
    have hp : val WuPaper.ClassicalFourthData.Bq 2150 = (169520284019128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2150 = 169520284019128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2150 = (203:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2151) ≤ val WuPaper.ClassicalFourthData.Bq 2151
    have hp : val WuPaper.ClassicalFourthData.Bq 2151 = (169567652095889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2151 = 169567652095889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2151 = (10151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2152) ≤ val WuPaper.ClassicalFourthData.Bq 2152
    have hp : val WuPaper.ClassicalFourthData.Bq 2152 = (169615000426893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2152 = 169615000426893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2152 = (1269:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2153) ≤ val WuPaper.ClassicalFourthData.Bq 2153
    have hp : val WuPaper.ClassicalFourthData.Bq 2153 = (169662329021359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2153 = 169662329021359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2153 = (10153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2154) ≤ val WuPaper.ClassicalFourthData.Bq 2154
    have hp : val WuPaper.ClassicalFourthData.Bq 2154 = (169709637888501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2154 = 169709637888501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2154 = (5077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2155) ≤ val WuPaper.ClassicalFourthData.Bq 2155
    have hp : val WuPaper.ClassicalFourthData.Bq 2155 = (169756927037529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2155 = 169756927037529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2155 = (2031:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2156) ≤ val WuPaper.ClassicalFourthData.Bq 2156
    have hp : val WuPaper.ClassicalFourthData.Bq 2156 = (169804196477646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2156 = 169804196477646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2156 = (2539:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2157) ≤ val WuPaper.ClassicalFourthData.Bq 2157
    have hp : val WuPaper.ClassicalFourthData.Bq 2157 = (169851446218050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2157 = 169851446218050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2157 = (10157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2158) ≤ val WuPaper.ClassicalFourthData.Bq 2158
    have hp : val WuPaper.ClassicalFourthData.Bq 2158 = (169898676267934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2158 = 169898676267934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2158 = (5079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2159) ≤ val WuPaper.ClassicalFourthData.Bq 2159
    have hp : val WuPaper.ClassicalFourthData.Bq 2159 = (169945886636487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2159 = 169945886636487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2159 = (10159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_134
