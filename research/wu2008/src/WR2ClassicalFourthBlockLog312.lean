import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints312
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_312 (j : Fin 16) (hj : 16*312+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*312+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*312+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4992) ≤ val WuPaper.ClassicalFourthData.Bq 4992
    have hp : val WuPaper.ClassicalFourthData.Bq 4992 = (249396838679633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4992 = 249396838679633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4992 = (406:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4993) ≤ val WuPaper.ClassicalFourthData.Bq 4993
    have hp : val WuPaper.ClassicalFourthData.Bq 4993 = (249411878954049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4993 = 249411878954049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4993 = (12993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4994) ≤ val WuPaper.ClassicalFourthData.Bq 4994
    have hp : val WuPaper.ClassicalFourthData.Bq 4994 = (249426913107166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4994 = 249426913107166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4994 = (6497:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4995) ≤ val WuPaper.ClassicalFourthData.Bq 4995
    have hp : val WuPaper.ClassicalFourthData.Bq 4995 = (249441941141241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4995 = 249441941141241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4995 = (2599:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4996) ≤ val WuPaper.ClassicalFourthData.Bq 4996
    have hp : val WuPaper.ClassicalFourthData.Bq 4996 = (249456963058535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4996 = 249456963058535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4996 = (3249:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4997) ≤ val WuPaper.ClassicalFourthData.Bq 4997
    have hp : val WuPaper.ClassicalFourthData.Bq 4997 = (249471978861304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4997 = 249471978861304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4997 = (12997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4998) ≤ val WuPaper.ClassicalFourthData.Bq 4998
    have hp : val WuPaper.ClassicalFourthData.Bq 4998 = (249486988551806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4998 = 249486988551806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4998 = (6499:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4999) ≤ val WuPaper.ClassicalFourthData.Bq 4999
    have hp : val WuPaper.ClassicalFourthData.Bq 4999 = (249501992132294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4999 = 249501992132294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4999 = (12999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4999
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5000) ≤ val WuPaper.ClassicalFourthData.Bq 5000
    have hp : val WuPaper.ClassicalFourthData.Bq 5000 = (249516989605025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5000 = 249516989605025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5000 = (13:ℝ)/4 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5001) ≤ val WuPaper.ClassicalFourthData.Bq 5001
    have hp : val WuPaper.ClassicalFourthData.Bq 5001 = (249531980972251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5001 = 249531980972251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5001 = (13001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5002) ≤ val WuPaper.ClassicalFourthData.Bq 5002
    have hp : val WuPaper.ClassicalFourthData.Bq 5002 = (249546966236226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5002 = 249546966236226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5002 = (6501:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5003) ≤ val WuPaper.ClassicalFourthData.Bq 5003
    have hp : val WuPaper.ClassicalFourthData.Bq 5003 = (249561945399201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5003 = 249561945399201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5003 = (13003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5004) ≤ val WuPaper.ClassicalFourthData.Bq 5004
    have hp : val WuPaper.ClassicalFourthData.Bq 5004 = (249576918463426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5004 = 249576918463426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5004 = (3251:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5005) ≤ val WuPaper.ClassicalFourthData.Bq 5005
    have hp : val WuPaper.ClassicalFourthData.Bq 5005 = (249591885431151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5005 = 249591885431151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5005 = (2601:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5006) ≤ val WuPaper.ClassicalFourthData.Bq 5006
    have hp : val WuPaper.ClassicalFourthData.Bq 5006 = (249606846304626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5006 = 249606846304626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5006 = (6503:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5007) ≤ val WuPaper.ClassicalFourthData.Bq 5007
    have hp : val WuPaper.ClassicalFourthData.Bq 5007 = (249621801086097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5007 = 249621801086097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5007 = (13007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_312
