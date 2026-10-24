import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints136
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_136 (j : Fin 16) (hj : 16*136+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*136+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*136+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2176) ≤ val WuPaper.ClassicalFourthData.Bq 2176
    have hp : val WuPaper.ClassicalFourthData.Bq 2176 = (170745460535608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2176 = 170745460535608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2176 = (318:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2177) ≤ val WuPaper.ClassicalFourthData.Bq 2177
    have hp : val WuPaper.ClassicalFourthData.Bq 2177 = (170792318205315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2177 = 170792318205315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2177 = (10177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2178) ≤ val WuPaper.ClassicalFourthData.Bq 2178
    have hp : val WuPaper.ClassicalFourthData.Bq 2178 = (170839156367263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2178 = 170839156367263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2178 = (5089:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2179) ≤ val WuPaper.ClassicalFourthData.Bq 2179
    have hp : val WuPaper.ClassicalFourthData.Bq 2179 = (170885975030535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2179 = 170885975030535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2179 = (10179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2180) ≤ val WuPaper.ClassicalFourthData.Bq 2180
    have hp : val WuPaper.ClassicalFourthData.Bq 2180 = (170932774204208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2180 = 170932774204208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2180 = (509:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2181) ≤ val WuPaper.ClassicalFourthData.Bq 2181
    have hp : val WuPaper.ClassicalFourthData.Bq 2181 = (170979553897357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2181 = 170979553897357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2181 = (10181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2182) ≤ val WuPaper.ClassicalFourthData.Bq 2182
    have hp : val WuPaper.ClassicalFourthData.Bq 2182 = (171026314119047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2182 = 171026314119047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2182 = (5091:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2183) ≤ val WuPaper.ClassicalFourthData.Bq 2183
    have hp : val WuPaper.ClassicalFourthData.Bq 2183 = (171073054878343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2183 = 171073054878343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2183 = (10183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2183
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2184) ≤ val WuPaper.ClassicalFourthData.Bq 2184
    have hp : val WuPaper.ClassicalFourthData.Bq 2184 = (171119776184301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2184 = 171119776184301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2184 = (1273:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2184
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2185) ≤ val WuPaper.ClassicalFourthData.Bq 2185
    have hp : val WuPaper.ClassicalFourthData.Bq 2185 = (171166478045974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2185 = 171166478045974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2185 = (2037:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2185
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2186) ≤ val WuPaper.ClassicalFourthData.Bq 2186
    have hp : val WuPaper.ClassicalFourthData.Bq 2186 = (171213160472409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2186 = 171213160472409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2186 = (5093:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2186
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2187) ≤ val WuPaper.ClassicalFourthData.Bq 2187
    have hp : val WuPaper.ClassicalFourthData.Bq 2187 = (171259823472646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2187 = 171259823472646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2187 = (10187:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2187
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2188) ≤ val WuPaper.ClassicalFourthData.Bq 2188
    have hp : val WuPaper.ClassicalFourthData.Bq 2188 = (171306467055725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2188 = 171306467055725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2188 = (2547:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2188
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2189) ≤ val WuPaper.ClassicalFourthData.Bq 2189
    have hp : val WuPaper.ClassicalFourthData.Bq 2189 = (171353091230674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2189 = 171353091230674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2189 = (10189:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2189
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2190) ≤ val WuPaper.ClassicalFourthData.Bq 2190
    have hp : val WuPaper.ClassicalFourthData.Bq 2190 = (171399696006522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2190 = 171399696006522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2190 = (1019:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2190
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2191) ≤ val WuPaper.ClassicalFourthData.Bq 2191
    have hp : val WuPaper.ClassicalFourthData.Bq 2191 = (171446281392290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2191 = 171446281392290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2191 = (10191:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2191
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_136
