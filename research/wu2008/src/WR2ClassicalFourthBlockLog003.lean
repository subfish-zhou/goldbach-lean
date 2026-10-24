import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints003
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_003 (j : Fin 16) (hj : 16*3+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*3+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*3+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 48) ≤ val WuPaper.ClassicalFourthData.Bq 48
    have hp : val WuPaper.ClassicalFourthData.Bq 48 = (5928713153715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 48 = 5928713153715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 48 = (503:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_48
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 49) ≤ val WuPaper.ClassicalFourthData.Bq 49
    have hp : val WuPaper.ClassicalFourthData.Bq 49 = (6050727260596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 49 = 6050727260596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 49 = (8049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_49
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 50) ≤ val WuPaper.ClassicalFourthData.Bq 50
    have hp : val WuPaper.ClassicalFourthData.Bq 50 = (6172680744625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 50 = 6172680744625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 50 = (161:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_50
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 51) ≤ val WuPaper.ClassicalFourthData.Bq 51
    have hp : val WuPaper.ClassicalFourthData.Bq 51 = (6294573643356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 51 = 6294573643356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 51 = (8051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_51
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 52) ≤ val WuPaper.ClassicalFourthData.Bq 52
    have hp : val WuPaper.ClassicalFourthData.Bq 52 = (6416405994311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 52 = 6416405994311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 52 = (2013:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_52
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 53) ≤ val WuPaper.ClassicalFourthData.Bq 53
    have hp : val WuPaper.ClassicalFourthData.Bq 53 = (6538177834984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 53 = 6538177834984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 53 = (8053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_53
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 54) ≤ val WuPaper.ClassicalFourthData.Bq 54
    have hp : val WuPaper.ClassicalFourthData.Bq 54 = (6659889202840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 54 = 6659889202840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 54 = (4027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_54
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 55) ≤ val WuPaper.ClassicalFourthData.Bq 55
    have hp : val WuPaper.ClassicalFourthData.Bq 55 = (6781540135313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 55 = 6781540135313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 55 = (1611:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_55
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 56) ≤ val WuPaper.ClassicalFourthData.Bq 56
    have hp : val WuPaper.ClassicalFourthData.Bq 56 = (6903130669808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 56 = 6903130669808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 56 = (1007:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_56
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 57) ≤ val WuPaper.ClassicalFourthData.Bq 57
    have hp : val WuPaper.ClassicalFourthData.Bq 57 = (7024660843699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 57 = 7024660843699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 57 = (8057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_57
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 58) ≤ val WuPaper.ClassicalFourthData.Bq 58
    have hp : val WuPaper.ClassicalFourthData.Bq 58 = (7146130694333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 58 = 7146130694333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 58 = (4029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_58
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 59) ≤ val WuPaper.ClassicalFourthData.Bq 59
    have hp : val WuPaper.ClassicalFourthData.Bq 59 = (7267540259025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 59 = 7267540259025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 59 = (8059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_59
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 60) ≤ val WuPaper.ClassicalFourthData.Bq 60
    have hp : val WuPaper.ClassicalFourthData.Bq 60 = (7388889575063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 60 = 7388889575063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 60 = (403:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_60
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 61) ≤ val WuPaper.ClassicalFourthData.Bq 61
    have hp : val WuPaper.ClassicalFourthData.Bq 61 = (7510178679703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 61 = 7510178679703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 61 = (8061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_61
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 62) ≤ val WuPaper.ClassicalFourthData.Bq 62
    have hp : val WuPaper.ClassicalFourthData.Bq 62 = (7631407610173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 62 = 7631407610173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 62 = (4031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_62
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 63) ≤ val WuPaper.ClassicalFourthData.Bq 63
    have hp : val WuPaper.ClassicalFourthData.Bq 63 = (7752576403671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 63 = 7752576403671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 63 = (8063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_63
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_003
