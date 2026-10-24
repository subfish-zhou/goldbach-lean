import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints628
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_628 (j : Fin 16) (hj : 16*628+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*628+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*628+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10048) ≤ val WuPaper.ClassicalFourthData.Bq 10048
    have hp : val WuPaper.ClassicalFourthData.Bq 10048 = (278409945894386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10048 = 278409945894386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10048 = (564:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10049) ≤ val WuPaper.ClassicalFourthData.Bq 10049
    have hp : val WuPaper.ClassicalFourthData.Bq 10049 = (278410295939361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10049 = 278410295939361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10049 = (18049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10050) ≤ val WuPaper.ClassicalFourthData.Bq 10050
    have hp : val WuPaper.ClassicalFourthData.Bq 10050 = (278410644822777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10050 = 278410644822777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10050 = (361:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10051) ≤ val WuPaper.ClassicalFourthData.Bq 10051
    have hp : val WuPaper.ClassicalFourthData.Bq 10051 = (278410992544987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10051 = 278410992544987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10051 = (18051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10052) ≤ val WuPaper.ClassicalFourthData.Bq 10052
    have hp : val WuPaper.ClassicalFourthData.Bq 10052 = (278411339106343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10052 = 278411339106343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10052 = (4513:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10053) ≤ val WuPaper.ClassicalFourthData.Bq 10053
    have hp : val WuPaper.ClassicalFourthData.Bq 10053 = (278411684507198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10053 = 278411684507198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10053 = (18053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10054) ≤ val WuPaper.ClassicalFourthData.Bq 10054
    have hp : val WuPaper.ClassicalFourthData.Bq 10054 = (278412028747906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10054 = 278412028747906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10054 = (9027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10055) ≤ val WuPaper.ClassicalFourthData.Bq 10055
    have hp : val WuPaper.ClassicalFourthData.Bq 10055 = (278412371828817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10055 = 278412371828817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10055 = (3611:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10055
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10056) ≤ val WuPaper.ClassicalFourthData.Bq 10056
    have hp : val WuPaper.ClassicalFourthData.Bq 10056 = (278412713750284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10056 = 278412713750284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10056 = (2257:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10057) ≤ val WuPaper.ClassicalFourthData.Bq 10057
    have hp : val WuPaper.ClassicalFourthData.Bq 10057 = (278413054512660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10057 = 278413054512660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10057 = (18057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10058) ≤ val WuPaper.ClassicalFourthData.Bq 10058
    have hp : val WuPaper.ClassicalFourthData.Bq 10058 = (278413394116297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10058 = 278413394116297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10058 = (9029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10059) ≤ val WuPaper.ClassicalFourthData.Bq 10059
    have hp : val WuPaper.ClassicalFourthData.Bq 10059 = (278413732561546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10059 = 278413732561546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10059 = (18059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10060) ≤ val WuPaper.ClassicalFourthData.Bq 10060
    have hp : val WuPaper.ClassicalFourthData.Bq 10060 = (278414069848760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10060 = 278414069848760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10060 = (903:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10061) ≤ val WuPaper.ClassicalFourthData.Bq 10061
    have hp : val WuPaper.ClassicalFourthData.Bq 10061 = (278414405978290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10061 = 278414405978290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10061 = (18061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10062) ≤ val WuPaper.ClassicalFourthData.Bq 10062
    have hp : val WuPaper.ClassicalFourthData.Bq 10062 = (278414740950487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10062 = 278414740950487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10062 = (9031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10063) ≤ val WuPaper.ClassicalFourthData.Bq 10063
    have hp : val WuPaper.ClassicalFourthData.Bq 10063 = (278415074765704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10063 = 278415074765704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10063 = (18063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_628
