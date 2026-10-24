import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints454
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_454 (j : Fin 16) (hj : 16*454+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*454+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*454+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7264) ≤ val WuPaper.ClassicalFourthData.Bq 7264
    have hp : val WuPaper.ClassicalFourthData.Bq 7264 = (271309601230683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7264 = 271309601230683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7264 = (477:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7265) ≤ val WuPaper.ClassicalFourthData.Bq 7265
    have hp : val WuPaper.ClassicalFourthData.Bq 7265 = (271315090144726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7265 = 271315090144726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7265 = (3053:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7266) ≤ val WuPaper.ClassicalFourthData.Bq 7266
    have hp : val WuPaper.ClassicalFourthData.Bq 7266 = (271320576274892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7266 = 271320576274892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7266 = (7633:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7267) ≤ val WuPaper.ClassicalFourthData.Bq 7267
    have hp : val WuPaper.ClassicalFourthData.Bq 7267 = (271326059622096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7267 = 271326059622096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7267 = (15267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7268) ≤ val WuPaper.ClassicalFourthData.Bq 7268
    have hp : val WuPaper.ClassicalFourthData.Bq 7268 = (271331540187250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7268 = 271331540187250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7268 = (3817:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7269) ≤ val WuPaper.ClassicalFourthData.Bq 7269
    have hp : val WuPaper.ClassicalFourthData.Bq 7269 = (271337017971267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7269 = 271337017971267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7269 = (15269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7270) ≤ val WuPaper.ClassicalFourthData.Bq 7270
    have hp : val WuPaper.ClassicalFourthData.Bq 7270 = (271342492975060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7270 = 271342492975060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7270 = (1527:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7271) ≤ val WuPaper.ClassicalFourthData.Bq 7271
    have hp : val WuPaper.ClassicalFourthData.Bq 7271 = (271347965199542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7271 = 271347965199542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7271 = (15271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7271
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7272) ≤ val WuPaper.ClassicalFourthData.Bq 7272
    have hp : val WuPaper.ClassicalFourthData.Bq 7272 = (271353434645623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7272 = 271353434645623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7272 = (1909:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7273) ≤ val WuPaper.ClassicalFourthData.Bq 7273
    have hp : val WuPaper.ClassicalFourthData.Bq 7273 = (271358901314216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7273 = 271358901314216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7273 = (15273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7274) ≤ val WuPaper.ClassicalFourthData.Bq 7274
    have hp : val WuPaper.ClassicalFourthData.Bq 7274 = (271364365206232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7274 = 271364365206232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7274 = (7637:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7275) ≤ val WuPaper.ClassicalFourthData.Bq 7275
    have hp : val WuPaper.ClassicalFourthData.Bq 7275 = (271369826322581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7275 = 271369826322581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7275 = (611:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7276) ≤ val WuPaper.ClassicalFourthData.Bq 7276
    have hp : val WuPaper.ClassicalFourthData.Bq 7276 = (271375284664174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7276 = 271375284664174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7276 = (3819:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7277) ≤ val WuPaper.ClassicalFourthData.Bq 7277
    have hp : val WuPaper.ClassicalFourthData.Bq 7277 = (271380740231922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7277 = 271380740231922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7277 = (15277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7278) ≤ val WuPaper.ClassicalFourthData.Bq 7278
    have hp : val WuPaper.ClassicalFourthData.Bq 7278 = (271386193026733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7278 = 271386193026733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7278 = (7639:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7279) ≤ val WuPaper.ClassicalFourthData.Bq 7279
    have hp : val WuPaper.ClassicalFourthData.Bq 7279 = (271391643049519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7279 = 271391643049519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7279 = (15279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_454
