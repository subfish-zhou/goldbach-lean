import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints451
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_451 (j : Fin 16) (hj : 16*451+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*451+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*451+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7216) ≤ val WuPaper.ClassicalFourthData.Bq 7216
    have hp : val WuPaper.ClassicalFourthData.Bq 7216 = (271042841528071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7216 = 271042841528071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7216 = (951:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7217) ≤ val WuPaper.ClassicalFourthData.Bq 7217
    have hp : val WuPaper.ClassicalFourthData.Bq 7217 = (271048465149145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7217 = 271048465149145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7217 = (15217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7218) ≤ val WuPaper.ClassicalFourthData.Bq 7218
    have hp : val WuPaper.ClassicalFourthData.Bq 7218 = (271054085942094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7218 = 271054085942094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7218 = (7609:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7219) ≤ val WuPaper.ClassicalFourthData.Bq 7219
    have hp : val WuPaper.ClassicalFourthData.Bq 7219 = (271059703907846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7219 = 271059703907846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7219 = (15219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7220) ≤ val WuPaper.ClassicalFourthData.Bq 7220
    have hp : val WuPaper.ClassicalFourthData.Bq 7220 = (271065319047333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7220 = 271065319047333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7220 = (761:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7221) ≤ val WuPaper.ClassicalFourthData.Bq 7221
    have hp : val WuPaper.ClassicalFourthData.Bq 7221 = (271070931361483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7221 = 271070931361483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7221 = (15221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7222) ≤ val WuPaper.ClassicalFourthData.Bq 7222
    have hp : val WuPaper.ClassicalFourthData.Bq 7222 = (271076540851224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7222 = 271076540851224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7222 = (7611:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7223) ≤ val WuPaper.ClassicalFourthData.Bq 7223
    have hp : val WuPaper.ClassicalFourthData.Bq 7223 = (271082147517487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7223 = 271082147517487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7223 = (15223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7223
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7224) ≤ val WuPaper.ClassicalFourthData.Bq 7224
    have hp : val WuPaper.ClassicalFourthData.Bq 7224 = (271087751361197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7224 = 271087751361197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7224 = (1903:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7225) ≤ val WuPaper.ClassicalFourthData.Bq 7225
    have hp : val WuPaper.ClassicalFourthData.Bq 7225 = (271093352383284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7225 = 271093352383284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7225 = (609:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7226) ≤ val WuPaper.ClassicalFourthData.Bq 7226
    have hp : val WuPaper.ClassicalFourthData.Bq 7226 = (271098950584675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7226 = 271098950584675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7226 = (7613:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7227) ≤ val WuPaper.ClassicalFourthData.Bq 7227
    have hp : val WuPaper.ClassicalFourthData.Bq 7227 = (271104545966297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7227 = 271104545966297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7227 = (15227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7228) ≤ val WuPaper.ClassicalFourthData.Bq 7228
    have hp : val WuPaper.ClassicalFourthData.Bq 7228 = (271110138529077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7228 = 271110138529077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7228 = (3807:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7229) ≤ val WuPaper.ClassicalFourthData.Bq 7229
    have hp : val WuPaper.ClassicalFourthData.Bq 7229 = (271115728273941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7229 = 271115728273941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7229 = (15229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7230) ≤ val WuPaper.ClassicalFourthData.Bq 7230
    have hp : val WuPaper.ClassicalFourthData.Bq 7230 = (271121315201816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7230 = 271121315201816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7230 = (1523:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7231) ≤ val WuPaper.ClassicalFourthData.Bq 7231
    have hp : val WuPaper.ClassicalFourthData.Bq 7231 = (271126899313627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7231 = 271126899313627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7231 = (15231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_451
