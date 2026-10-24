import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints634
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_634 (j : Fin 16) (hj : 16*634+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*634+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*634+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10144) ≤ val WuPaper.ClassicalFourthData.Bq 10144
    have hp : val WuPaper.ClassicalFourthData.Bq 10144 = (278438303548135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10144 = 278438303548135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10144 = (567:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10145) ≤ val WuPaper.ClassicalFourthData.Bq 10145
    have hp : val WuPaper.ClassicalFourthData.Bq 10145 = (278438543676553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10145 = 278438543676553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10145 = (3629:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10146) ≤ val WuPaper.ClassicalFourthData.Bq 10146
    have hp : val WuPaper.ClassicalFourthData.Bq 10146 = (278438782676780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10146 = 278438782676780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10146 = (9073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10147) ≤ val WuPaper.ClassicalFourthData.Bq 10147
    have hp : val WuPaper.ClassicalFourthData.Bq 10147 = (278439020549159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10147 = 278439020549159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10147 = (18147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10148) ≤ val WuPaper.ClassicalFourthData.Bq 10148
    have hp : val WuPaper.ClassicalFourthData.Bq 10148 = (278439257294030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10148 = 278439257294030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10148 = (4537:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10149) ≤ val WuPaper.ClassicalFourthData.Bq 10149
    have hp : val WuPaper.ClassicalFourthData.Bq 10149 = (278439492911737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10149 = 278439492911737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10149 = (18149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10150) ≤ val WuPaper.ClassicalFourthData.Bq 10150
    have hp : val WuPaper.ClassicalFourthData.Bq 10150 = (278439727402621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10150 = 278439727402621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10150 = (363:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10151) ≤ val WuPaper.ClassicalFourthData.Bq 10151
    have hp : val WuPaper.ClassicalFourthData.Bq 10151 = (278439960767024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10151 = 278439960767024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10151 = (18151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10152) ≤ val WuPaper.ClassicalFourthData.Bq 10152
    have hp : val WuPaper.ClassicalFourthData.Bq 10152 = (278440193005288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10152 = 278440193005288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10152 = (2269:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10153) ≤ val WuPaper.ClassicalFourthData.Bq 10153
    have hp : val WuPaper.ClassicalFourthData.Bq 10153 = (278440424117755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10153 = 278440424117755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10153 = (18153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10154) ≤ val WuPaper.ClassicalFourthData.Bq 10154
    have hp : val WuPaper.ClassicalFourthData.Bq 10154 = (278440654104765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10154 = 278440654104765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10154 = (9077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10155) ≤ val WuPaper.ClassicalFourthData.Bq 10155
    have hp : val WuPaper.ClassicalFourthData.Bq 10155 = (278440882966661:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10155 = 278440882966661 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10155 = (3631:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10156) ≤ val WuPaper.ClassicalFourthData.Bq 10156
    have hp : val WuPaper.ClassicalFourthData.Bq 10156 = (278441110703783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10156 = 278441110703783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10156 = (4539:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10157) ≤ val WuPaper.ClassicalFourthData.Bq 10157
    have hp : val WuPaper.ClassicalFourthData.Bq 10157 = (278441337316472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10157 = 278441337316472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10157 = (18157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10158) ≤ val WuPaper.ClassicalFourthData.Bq 10158
    have hp : val WuPaper.ClassicalFourthData.Bq 10158 = (278441562805071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10158 = 278441562805071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10158 = (9079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10159) ≤ val WuPaper.ClassicalFourthData.Bq 10159
    have hp : val WuPaper.ClassicalFourthData.Bq 10159 = (278441787169920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10159 = 278441787169920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10159 = (18159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_634
