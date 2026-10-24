import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints001
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_001 (j : Fin 16) (hj : 16*1+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*1+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*1+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 16) ≤ val WuPaper.ClassicalFourthData.Bq 16
    have hp : val WuPaper.ClassicalFourthData.Bq 16 = (1992026581606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 16 = 1992026581606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 16 = (501:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_16
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 17) ≤ val WuPaper.ClassicalFourthData.Bq 17
    have hp : val WuPaper.ClassicalFourthData.Bq 17 = (2116000627295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 17 = 2116000627295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 17 = (8017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_17
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 18) ≤ val WuPaper.ClassicalFourthData.Bq 18
    have hp : val WuPaper.ClassicalFourthData.Bq 18 = (2239912832553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 18 = 2239912832553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 18 = (4009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_18
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 19) ≤ val WuPaper.ClassicalFourthData.Bq 19
    have hp : val WuPaper.ClassicalFourthData.Bq 19 = (2363763235902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 19 = 2363763235902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 19 = (8019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_19
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 20) ≤ val WuPaper.ClassicalFourthData.Bq 20
    have hp : val WuPaper.ClassicalFourthData.Bq 20 = (2487551875830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 20 = 2487551875830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 20 = (401:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_20
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 21) ≤ val WuPaper.ClassicalFourthData.Bq 21
    have hp : val WuPaper.ClassicalFourthData.Bq 21 = (2611278790798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 21 = 2611278790798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 21 = (8021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_21
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 22) ≤ val WuPaper.ClassicalFourthData.Bq 22
    have hp : val WuPaper.ClassicalFourthData.Bq 22 = (2734944019232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 22 = 2734944019232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 22 = (4011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_22
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 23) ≤ val WuPaper.ClassicalFourthData.Bq 23
    have hp : val WuPaper.ClassicalFourthData.Bq 23 = (2858547599532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 23 = 2858547599532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 23 = (8023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_23
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 24) ≤ val WuPaper.ClassicalFourthData.Bq 24
    have hp : val WuPaper.ClassicalFourthData.Bq 24 = (2982089570064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 24 = 2982089570064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 24 = (1003:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_24
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 25) ≤ val WuPaper.ClassicalFourthData.Bq 25
    have hp : val WuPaper.ClassicalFourthData.Bq 25 = (3105569969165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 25 = 3105569969165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 25 = (321:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_25
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 26) ≤ val WuPaper.ClassicalFourthData.Bq 26
    have hp : val WuPaper.ClassicalFourthData.Bq 26 = (3228988835141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 26 = 3228988835141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 26 = (4013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_26
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 27) ≤ val WuPaper.ClassicalFourthData.Bq 27
    have hp : val WuPaper.ClassicalFourthData.Bq 27 = (3352346206268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 27 = 3352346206268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 27 = (8027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_27
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 28) ≤ val WuPaper.ClassicalFourthData.Bq 28
    have hp : val WuPaper.ClassicalFourthData.Bq 28 = (3475642120790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 28 = 3475642120790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 28 = (2007:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_28
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 29) ≤ val WuPaper.ClassicalFourthData.Bq 29
    have hp : val WuPaper.ClassicalFourthData.Bq 29 = (3598876616924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 29 = 3598876616924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 29 = (8029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_29
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 30) ≤ val WuPaper.ClassicalFourthData.Bq 30
    have hp : val WuPaper.ClassicalFourthData.Bq 30 = (3722049732853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 30 = 3722049732853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 30 = (803:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_30
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 31) ≤ val WuPaper.ClassicalFourthData.Bq 31
    have hp : val WuPaper.ClassicalFourthData.Bq 31 = (3845161506731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 31 = 3845161506731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 31 = (8031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_31
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_001
