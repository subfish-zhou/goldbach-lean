import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints138
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_138 (j : Fin 16) (hj : 16*138+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*138+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*138+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2208) ≤ val WuPaper.ClassicalFourthData.Bq 2208
    have hp : val WuPaper.ClassicalFourthData.Bq 2208 = (172235274984729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2208 = 172235274984729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2208 = (319:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2209) ≤ val WuPaper.ClassicalFourthData.Bq 2209
    have hp : val WuPaper.ClassicalFourthData.Bq 2209 = (172281512885833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2209 = 172281512885833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2209 = (10209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2210) ≤ val WuPaper.ClassicalFourthData.Bq 2210
    have hp : val WuPaper.ClassicalFourthData.Bq 2210 = (172327731567286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2210 = 172327731567286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2210 = (1021:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2211) ≤ val WuPaper.ClassicalFourthData.Bq 2211
    have hp : val WuPaper.ClassicalFourthData.Bq 2211 = (172373931038009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2211 = 172373931038009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2211 = (10211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2212) ≤ val WuPaper.ClassicalFourthData.Bq 2212
    have hp : val WuPaper.ClassicalFourthData.Bq 2212 = (172420111306914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2212 = 172420111306914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2212 = (2553:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2213) ≤ val WuPaper.ClassicalFourthData.Bq 2213
    have hp : val WuPaper.ClassicalFourthData.Bq 2213 = (172466272382911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2213 = 172466272382911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2213 = (10213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2214) ≤ val WuPaper.ClassicalFourthData.Bq 2214
    have hp : val WuPaper.ClassicalFourthData.Bq 2214 = (172512414274904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2214 = 172512414274904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2214 = (5107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2215) ≤ val WuPaper.ClassicalFourthData.Bq 2215
    have hp : val WuPaper.ClassicalFourthData.Bq 2215 = (172558536991791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2215 = 172558536991791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2215 = (2043:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2216) ≤ val WuPaper.ClassicalFourthData.Bq 2216
    have hp : val WuPaper.ClassicalFourthData.Bq 2216 = (172604640542466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2216 = 172604640542466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2216 = (1277:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2217) ≤ val WuPaper.ClassicalFourthData.Bq 2217
    have hp : val WuPaper.ClassicalFourthData.Bq 2217 = (172650724935817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2217 = 172650724935817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2217 = (10217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2218) ≤ val WuPaper.ClassicalFourthData.Bq 2218
    have hp : val WuPaper.ClassicalFourthData.Bq 2218 = (172696790180729:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2218 = 172696790180729 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2218 = (5109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2219) ≤ val WuPaper.ClassicalFourthData.Bq 2219
    have hp : val WuPaper.ClassicalFourthData.Bq 2219 = (172742836286080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2219 = 172742836286080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2219 = (10219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2220) ≤ val WuPaper.ClassicalFourthData.Bq 2220
    have hp : val WuPaper.ClassicalFourthData.Bq 2220 = (172788863260743:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2220 = 172788863260743 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2220 = (511:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2221) ≤ val WuPaper.ClassicalFourthData.Bq 2221
    have hp : val WuPaper.ClassicalFourthData.Bq 2221 = (172834871113587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2221 = 172834871113587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2221 = (10221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2222) ≤ val WuPaper.ClassicalFourthData.Bq 2222
    have hp : val WuPaper.ClassicalFourthData.Bq 2222 = (172880859853475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2222 = 172880859853475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2222 = (5111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2223) ≤ val WuPaper.ClassicalFourthData.Bq 2223
    have hp : val WuPaper.ClassicalFourthData.Bq 2223 = (172926829489266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2223 = 172926829489266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2223 = (10223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_138
