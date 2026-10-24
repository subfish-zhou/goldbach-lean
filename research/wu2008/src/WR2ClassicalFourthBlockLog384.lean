import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints384
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_384 (j : Fin 16) (hj : 16*384+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*384+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*384+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6144) ≤ val WuPaper.ClassicalFourthData.Bq 6144
    have hp : val WuPaper.ClassicalFourthData.Bq 6144 = (263175349710126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6144 = 263175349710126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6144 = (442:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6145) ≤ val WuPaper.ClassicalFourthData.Bq 6145
    have hp : val WuPaper.ClassicalFourthData.Bq 6145 = (263184619910333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6145 = 263184619910333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6145 = (2829:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6146) ≤ val WuPaper.ClassicalFourthData.Bq 6146
    have hp : val WuPaper.ClassicalFourthData.Bq 6146 = (263193886052491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6146 = 263193886052491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6146 = (7073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6147) ≤ val WuPaper.ClassicalFourthData.Bq 6147
    have hp : val WuPaper.ClassicalFourthData.Bq 6147 = (263203148138003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6147 = 263203148138003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6147 = (14147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6148) ≤ val WuPaper.ClassicalFourthData.Bq 6148
    have hp : val WuPaper.ClassicalFourthData.Bq 6148 = (263212406168270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6148 = 263212406168270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6148 = (3537:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6149) ≤ val WuPaper.ClassicalFourthData.Bq 6149
    have hp : val WuPaper.ClassicalFourthData.Bq 6149 = (263221660144694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6149 = 263221660144694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6149 = (14149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6150) ≤ val WuPaper.ClassicalFourthData.Bq 6150
    have hp : val WuPaper.ClassicalFourthData.Bq 6150 = (263230910068674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6150 = 263230910068674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6150 = (283:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6151) ≤ val WuPaper.ClassicalFourthData.Bq 6151
    have hp : val WuPaper.ClassicalFourthData.Bq 6151 = (263240155941610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6151 = 263240155941610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6151 = (14151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6152) ≤ val WuPaper.ClassicalFourthData.Bq 6152
    have hp : val WuPaper.ClassicalFourthData.Bq 6152 = (263249397764902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6152 = 263249397764902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6152 = (1769:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6153) ≤ val WuPaper.ClassicalFourthData.Bq 6153
    have hp : val WuPaper.ClassicalFourthData.Bq 6153 = (263258635539948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6153 = 263258635539948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6153 = (14153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6154) ≤ val WuPaper.ClassicalFourthData.Bq 6154
    have hp : val WuPaper.ClassicalFourthData.Bq 6154 = (263267869268147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6154 = 263267869268147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6154 = (7077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6155) ≤ val WuPaper.ClassicalFourthData.Bq 6155
    have hp : val WuPaper.ClassicalFourthData.Bq 6155 = (263277098950897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6155 = 263277098950897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6155 = (2831:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6156) ≤ val WuPaper.ClassicalFourthData.Bq 6156
    have hp : val WuPaper.ClassicalFourthData.Bq 6156 = (263286324589593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6156 = 263286324589593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6156 = (3539:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6157) ≤ val WuPaper.ClassicalFourthData.Bq 6157
    have hp : val WuPaper.ClassicalFourthData.Bq 6157 = (263295546185633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6157 = 263295546185633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6157 = (14157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6158) ≤ val WuPaper.ClassicalFourthData.Bq 6158
    have hp : val WuPaper.ClassicalFourthData.Bq 6158 = (263304763740413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6158 = 263304763740413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6158 = (7079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6159) ≤ val WuPaper.ClassicalFourthData.Bq 6159
    have hp : val WuPaper.ClassicalFourthData.Bq 6159 = (263313977255327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6159 = 263313977255327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6159 = (14159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_384
