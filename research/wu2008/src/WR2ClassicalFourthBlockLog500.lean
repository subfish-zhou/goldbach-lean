import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints500
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_500 (j : Fin 16) (hj : 16*500+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*500+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*500+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8000) ≤ val WuPaper.ClassicalFourthData.Bq 8000
    have hp : val WuPaper.ClassicalFourthData.Bq 8000 = (274653072167665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8000 = 274653072167665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8000 = (4:ℝ)/1 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8001) ≤ val WuPaper.ClassicalFourthData.Bq 8001
    have hp : val WuPaper.ClassicalFourthData.Bq 8001 = (274656738586831:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8001 = 274656738586831 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8001 = (16001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8002) ≤ val WuPaper.ClassicalFourthData.Bq 8002
    have hp : val WuPaper.ClassicalFourthData.Bq 8002 = (274660402812147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8002 = 274660402812147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8002 = (8001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8003) ≤ val WuPaper.ClassicalFourthData.Bq 8003
    have hp : val WuPaper.ClassicalFourthData.Bq 8003 = (274664064844313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8003 = 274664064844313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8003 = (16003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8004) ≤ val WuPaper.ClassicalFourthData.Bq 8004
    have hp : val WuPaper.ClassicalFourthData.Bq 8004 = (274667724684030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8004 = 274667724684030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8004 = (4001:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8005) ≤ val WuPaper.ClassicalFourthData.Bq 8005
    have hp : val WuPaper.ClassicalFourthData.Bq 8005 = (274671382331998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8005 = 274671382331998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8005 = (3201:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8006) ≤ val WuPaper.ClassicalFourthData.Bq 8006
    have hp : val WuPaper.ClassicalFourthData.Bq 8006 = (274675037788916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8006 = 274675037788916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8006 = (8003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8007) ≤ val WuPaper.ClassicalFourthData.Bq 8007
    have hp : val WuPaper.ClassicalFourthData.Bq 8007 = (274678691055483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8007 = 274678691055483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8007 = (16007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8007
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8008) ≤ val WuPaper.ClassicalFourthData.Bq 8008
    have hp : val WuPaper.ClassicalFourthData.Bq 8008 = (274682342132400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8008 = 274682342132400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8008 = (2001:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8009) ≤ val WuPaper.ClassicalFourthData.Bq 8009
    have hp : val WuPaper.ClassicalFourthData.Bq 8009 = (274685991020365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8009 = 274685991020365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8009 = (16009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8010) ≤ val WuPaper.ClassicalFourthData.Bq 8010
    have hp : val WuPaper.ClassicalFourthData.Bq 8010 = (274689637720077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8010 = 274689637720077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8010 = (1601:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8011) ≤ val WuPaper.ClassicalFourthData.Bq 8011
    have hp : val WuPaper.ClassicalFourthData.Bq 8011 = (274693282232234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8011 = 274693282232234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8011 = (16011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8012) ≤ val WuPaper.ClassicalFourthData.Bq 8012
    have hp : val WuPaper.ClassicalFourthData.Bq 8012 = (274696924557535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8012 = 274696924557535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8012 = (4003:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8013) ≤ val WuPaper.ClassicalFourthData.Bq 8013
    have hp : val WuPaper.ClassicalFourthData.Bq 8013 = (274700564696677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8013 = 274700564696677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8013 = (16013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8014) ≤ val WuPaper.ClassicalFourthData.Bq 8014
    have hp : val WuPaper.ClassicalFourthData.Bq 8014 = (274704202650358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8014 = 274704202650358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8014 = (8007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8015) ≤ val WuPaper.ClassicalFourthData.Bq 8015
    have hp : val WuPaper.ClassicalFourthData.Bq 8015 = (274707838419276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8015 = 274707838419276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8015 = (3203:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_500
