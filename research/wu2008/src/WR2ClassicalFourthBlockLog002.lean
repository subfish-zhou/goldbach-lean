import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints002
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_002 (j : Fin 16) (hj : 16*2+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*2+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*2+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 32) ≤ val WuPaper.ClassicalFourthData.Bq 32
    have hp : val WuPaper.ClassicalFourthData.Bq 32 = (3968211976682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 32 = 3968211976682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 32 = (251:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_32
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 33) ≤ val WuPaper.ClassicalFourthData.Bq 33
    have hp : val WuPaper.ClassicalFourthData.Bq 33 = (4091201180800:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 33 = 4091201180800 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 33 = (8033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_33
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 34) ≤ val WuPaper.ClassicalFourthData.Bq 34
    have hp : val WuPaper.ClassicalFourthData.Bq 34 = (4214129157147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 34 = 4214129157147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 34 = (4017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_34
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 35) ≤ val WuPaper.ClassicalFourthData.Bq 35
    have hp : val WuPaper.ClassicalFourthData.Bq 35 = (4336995943757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 35 = 4336995943757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 35 = (1607:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_35
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 36) ≤ val WuPaper.ClassicalFourthData.Bq 36
    have hp : val WuPaper.ClassicalFourthData.Bq 36 = (4459801578633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 36 = 4459801578633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 36 = (2009:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_36
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 37) ≤ val WuPaper.ClassicalFourthData.Bq 37
    have hp : val WuPaper.ClassicalFourthData.Bq 37 = (4582546099746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 37 = 4582546099746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 37 = (8037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_37
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 38) ≤ val WuPaper.ClassicalFourthData.Bq 38
    have hp : val WuPaper.ClassicalFourthData.Bq 38 = (4705229545039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 38 = 4705229545039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 38 = (4019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_38
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 39) ≤ val WuPaper.ClassicalFourthData.Bq 39
    have hp : val WuPaper.ClassicalFourthData.Bq 39 = (4827851952425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 39 = 4827851952425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 39 = (8039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_39
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 40) ≤ val WuPaper.ClassicalFourthData.Bq 40
    have hp : val WuPaper.ClassicalFourthData.Bq 40 = (4950413359786:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 40 = 4950413359786 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 40 = (201:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_40
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 41) ≤ val WuPaper.ClassicalFourthData.Bq 41
    have hp : val WuPaper.ClassicalFourthData.Bq 41 = (5072913804973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 41 = 5072913804973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 41 = (8041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_41
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 42) ≤ val WuPaper.ClassicalFourthData.Bq 42
    have hp : val WuPaper.ClassicalFourthData.Bq 42 = (5195353325809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 42 = 5195353325809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 42 = (4021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_42
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 43) ≤ val WuPaper.ClassicalFourthData.Bq 43
    have hp : val WuPaper.ClassicalFourthData.Bq 43 = (5317731960087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 43 = 5317731960087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 43 = (8043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_43
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 44) ≤ val WuPaper.ClassicalFourthData.Bq 44
    have hp : val WuPaper.ClassicalFourthData.Bq 44 = (5440049745567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 44 = 5440049745567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 44 = (2011:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_44
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 45) ≤ val WuPaper.ClassicalFourthData.Bq 45
    have hp : val WuPaper.ClassicalFourthData.Bq 45 = (5562306719983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 45 = 5562306719983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 45 = (1609:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_45
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 46) ≤ val WuPaper.ClassicalFourthData.Bq 46
    have hp : val WuPaper.ClassicalFourthData.Bq 46 = (5684502921036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 46 = 5684502921036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 46 = (4023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_46
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 47) ≤ val WuPaper.ClassicalFourthData.Bq 47
    have hp : val WuPaper.ClassicalFourthData.Bq 47 = (5806638386399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 47 = 5806638386399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 47 = (8047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_47
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_002
