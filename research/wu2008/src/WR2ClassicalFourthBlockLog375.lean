import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints375
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_375 (j : Fin 16) (hj : 16*375+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*375+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*375+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6000) ≤ val WuPaper.ClassicalFourthData.Bq 6000
    have hp : val WuPaper.ClassicalFourthData.Bq 6000 = (261797351964049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6000 = 261797351964049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6000 = (7:ℝ)/2 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6001) ≤ val WuPaper.ClassicalFourthData.Bq 6001
    have hp : val WuPaper.ClassicalFourthData.Bq 6001 = (261807221448327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6001 = 261807221448327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6001 = (14001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6002) ≤ val WuPaper.ClassicalFourthData.Bq 6002
    have hp : val WuPaper.ClassicalFourthData.Bq 6002 = (261817086666716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6002 = 261817086666716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6002 = (7001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6003) ≤ val WuPaper.ClassicalFourthData.Bq 6003
    have hp : val WuPaper.ClassicalFourthData.Bq 6003 = (261826947620702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6003 = 261826947620702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6003 = (14003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6004) ≤ val WuPaper.ClassicalFourthData.Bq 6004
    have hp : val WuPaper.ClassicalFourthData.Bq 6004 = (261836804311768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6004 = 261836804311768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6004 = (3501:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6005) ≤ val WuPaper.ClassicalFourthData.Bq 6005
    have hp : val WuPaper.ClassicalFourthData.Bq 6005 = (261846656741399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6005 = 261846656741399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6005 = (2801:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6006) ≤ val WuPaper.ClassicalFourthData.Bq 6006
    have hp : val WuPaper.ClassicalFourthData.Bq 6006 = (261856504911078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6006 = 261856504911078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6006 = (7003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6007) ≤ val WuPaper.ClassicalFourthData.Bq 6007
    have hp : val WuPaper.ClassicalFourthData.Bq 6007 = (261866348822288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6007 = 261866348822288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6007 = (14007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6007
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6008) ≤ val WuPaper.ClassicalFourthData.Bq 6008
    have hp : val WuPaper.ClassicalFourthData.Bq 6008 = (261876188476510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6008 = 261876188476510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6008 = (1751:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6009) ≤ val WuPaper.ClassicalFourthData.Bq 6009
    have hp : val WuPaper.ClassicalFourthData.Bq 6009 = (261886023875226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6009 = 261886023875226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6009 = (14009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6010) ≤ val WuPaper.ClassicalFourthData.Bq 6010
    have hp : val WuPaper.ClassicalFourthData.Bq 6010 = (261895855019916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6010 = 261895855019916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6010 = (1401:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6011) ≤ val WuPaper.ClassicalFourthData.Bq 6011
    have hp : val WuPaper.ClassicalFourthData.Bq 6011 = (261905681912062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6011 = 261905681912062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6011 = (14011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6012) ≤ val WuPaper.ClassicalFourthData.Bq 6012
    have hp : val WuPaper.ClassicalFourthData.Bq 6012 = (261915504553142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6012 = 261915504553142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6012 = (3503:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6013) ≤ val WuPaper.ClassicalFourthData.Bq 6013
    have hp : val WuPaper.ClassicalFourthData.Bq 6013 = (261925322944635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6013 = 261925322944635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6013 = (14013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6014) ≤ val WuPaper.ClassicalFourthData.Bq 6014
    have hp : val WuPaper.ClassicalFourthData.Bq 6014 = (261935137088021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6014 = 261935137088021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6014 = (7007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6015) ≤ val WuPaper.ClassicalFourthData.Bq 6015
    have hp : val WuPaper.ClassicalFourthData.Bq 6015 = (261944946984776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6015 = 261944946984776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6015 = (2803:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_375
