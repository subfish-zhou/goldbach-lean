import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints201
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_201 (j : Fin 16) (hj : 16*201+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*201+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*201+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3216) ≤ val WuPaper.ClassicalFourthData.Bq 3216
    have hp : val WuPaper.ClassicalFourthData.Bq 3216 = (210415984893165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3216 = 210415984893165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3216 = (701:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3217) ≤ val WuPaper.ClassicalFourthData.Bq 3217
    have hp : val WuPaper.ClassicalFourthData.Bq 3217 = (210446640980742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3217 = 210446640980742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3217 = (11217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3218) ≤ val WuPaper.ClassicalFourthData.Bq 3218
    have hp : val WuPaper.ClassicalFourthData.Bq 3218 = (210477284756893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3218 = 210477284756893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3218 = (5609:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3219) ≤ val WuPaper.ClassicalFourthData.Bq 3219
    have hp : val WuPaper.ClassicalFourthData.Bq 3219 = (210507916226806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3219 = 210507916226806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3219 = (11219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3220) ≤ val WuPaper.ClassicalFourthData.Bq 3220
    have hp : val WuPaper.ClassicalFourthData.Bq 3220 = (210538535395667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3220 = 210538535395667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3220 = (561:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3221) ≤ val WuPaper.ClassicalFourthData.Bq 3221
    have hp : val WuPaper.ClassicalFourthData.Bq 3221 = (210569142268659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3221 = 210569142268659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3221 = (11221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3222) ≤ val WuPaper.ClassicalFourthData.Bq 3222
    have hp : val WuPaper.ClassicalFourthData.Bq 3222 = (210599736850963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3222 = 210599736850963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3222 = (5611:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3223) ≤ val WuPaper.ClassicalFourthData.Bq 3223
    have hp : val WuPaper.ClassicalFourthData.Bq 3223 = (210630319147757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3223 = 210630319147757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3223 = (11223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3223
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3224) ≤ val WuPaper.ClassicalFourthData.Bq 3224
    have hp : val WuPaper.ClassicalFourthData.Bq 3224 = (210660889164218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3224 = 210660889164218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3224 = (1403:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3224
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3225) ≤ val WuPaper.ClassicalFourthData.Bq 3225
    have hp : val WuPaper.ClassicalFourthData.Bq 3225 = (210691446905517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3225 = 210691446905517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3225 = (449:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3225
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3226) ≤ val WuPaper.ClassicalFourthData.Bq 3226
    have hp : val WuPaper.ClassicalFourthData.Bq 3226 = (210721992376825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3226 = 210721992376825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3226 = (5613:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3226
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3227) ≤ val WuPaper.ClassicalFourthData.Bq 3227
    have hp : val WuPaper.ClassicalFourthData.Bq 3227 = (210752525583310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3227 = 210752525583310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3227 = (11227:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3227
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3228) ≤ val WuPaper.ClassicalFourthData.Bq 3228
    have hp : val WuPaper.ClassicalFourthData.Bq 3228 = (210783046530136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3228 = 210783046530136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3228 = (2807:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3228
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3229) ≤ val WuPaper.ClassicalFourthData.Bq 3229
    have hp : val WuPaper.ClassicalFourthData.Bq 3229 = (210813555222467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3229 = 210813555222467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3229 = (11229:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3229
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3230) ≤ val WuPaper.ClassicalFourthData.Bq 3230
    have hp : val WuPaper.ClassicalFourthData.Bq 3230 = (210844051665462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3230 = 210844051665462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3230 = (1123:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3230
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3231) ≤ val WuPaper.ClassicalFourthData.Bq 3231
    have hp : val WuPaper.ClassicalFourthData.Bq 3231 = (210874535864278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3231 = 210874535864278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3231 = (11231:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3231
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_201
