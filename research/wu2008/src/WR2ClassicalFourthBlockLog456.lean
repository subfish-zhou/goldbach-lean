import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints456
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_456 (j : Fin 16) (hj : 16*456+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*456+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*456+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7296) ≤ val WuPaper.ClassicalFourthData.Bq 7296
    have hp : val WuPaper.ClassicalFourthData.Bq 7296 = (271483870196529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7296 = 271483870196529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7296 = (478:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7297) ≤ val WuPaper.ClassicalFourthData.Bq 7297
    have hp : val WuPaper.ClassicalFourthData.Bq 7297 = (271489270477985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7297 = 271489270477985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7297 = (15297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7298) ≤ val WuPaper.ClassicalFourthData.Bq 7298
    have hp : val WuPaper.ClassicalFourthData.Bq 7298 = (271494668004631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7298 = 271494668004631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7298 = (7649:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7299) ≤ val WuPaper.ClassicalFourthData.Bq 7299
    have hp : val WuPaper.ClassicalFourthData.Bq 7299 = (271500062777372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7299 = 271500062777372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7299 = (15299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7300) ≤ val WuPaper.ClassicalFourthData.Bq 7300
    have hp : val WuPaper.ClassicalFourthData.Bq 7300 = (271505454797109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7300 = 271505454797109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7300 = (153:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7301) ≤ val WuPaper.ClassicalFourthData.Bq 7301
    have hp : val WuPaper.ClassicalFourthData.Bq 7301 = (271510844064744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7301 = 271510844064744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7301 = (15301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7302) ≤ val WuPaper.ClassicalFourthData.Bq 7302
    have hp : val WuPaper.ClassicalFourthData.Bq 7302 = (271516230581179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7302 = 271516230581179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7302 = (7651:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7303) ≤ val WuPaper.ClassicalFourthData.Bq 7303
    have hp : val WuPaper.ClassicalFourthData.Bq 7303 = (271521614347316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7303 = 271521614347316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7303 = (15303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7303
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7304) ≤ val WuPaper.ClassicalFourthData.Bq 7304
    have hp : val WuPaper.ClassicalFourthData.Bq 7304 = (271526995364056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7304 = 271526995364056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7304 = (1913:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7305) ≤ val WuPaper.ClassicalFourthData.Bq 7305
    have hp : val WuPaper.ClassicalFourthData.Bq 7305 = (271532373632299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7305 = 271532373632299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7305 = (3061:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7306) ≤ val WuPaper.ClassicalFourthData.Bq 7306
    have hp : val WuPaper.ClassicalFourthData.Bq 7306 = (271537749152947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7306 = 271537749152947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7306 = (7653:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7307) ≤ val WuPaper.ClassicalFourthData.Bq 7307
    have hp : val WuPaper.ClassicalFourthData.Bq 7307 = (271543121926899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7307 = 271543121926899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7307 = (15307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7308) ≤ val WuPaper.ClassicalFourthData.Bq 7308
    have hp : val WuPaper.ClassicalFourthData.Bq 7308 = (271548491955056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7308 = 271548491955056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7308 = (3827:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7309) ≤ val WuPaper.ClassicalFourthData.Bq 7309
    have hp : val WuPaper.ClassicalFourthData.Bq 7309 = (271553859238316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7309 = 271553859238316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7309 = (15309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7310) ≤ val WuPaper.ClassicalFourthData.Bq 7310
    have hp : val WuPaper.ClassicalFourthData.Bq 7310 = (271559223777580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7310 = 271559223777580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7310 = (1531:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7311) ≤ val WuPaper.ClassicalFourthData.Bq 7311
    have hp : val WuPaper.ClassicalFourthData.Bq 7311 = (271564585573745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7311 = 271564585573745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7311 = (15311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_456
