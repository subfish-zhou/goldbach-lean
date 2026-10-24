import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints429
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_429 (j : Fin 16) (hj : 16*429+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*429+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*429+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6864) ≤ val WuPaper.ClassicalFourthData.Bq 6864
    have hp : val WuPaper.ClassicalFourthData.Bq 6864 = (268880573115348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6864 = 268880573115348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6864 = (929:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6865) ≤ val WuPaper.ClassicalFourthData.Bq 6865
    have hp : val WuPaper.ClassicalFourthData.Bq 6865 = (268887252630659:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6865 = 268887252630659 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6865 = (2973:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6866) ≤ val WuPaper.ClassicalFourthData.Bq 6866
    have hp : val WuPaper.ClassicalFourthData.Bq 6866 = (268893928968014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6866 = 268893928968014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6866 = (7433:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6867) ≤ val WuPaper.ClassicalFourthData.Bq 6867
    have hp : val WuPaper.ClassicalFourthData.Bq 6867 = (268900602128475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6867 = 268900602128475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6867 = (14867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6868) ≤ val WuPaper.ClassicalFourthData.Bq 6868
    have hp : val WuPaper.ClassicalFourthData.Bq 6868 = (268907272113101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6868 = 268907272113101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6868 = (3717:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6869) ≤ val WuPaper.ClassicalFourthData.Bq 6869
    have hp : val WuPaper.ClassicalFourthData.Bq 6869 = (268913938922953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6869 = 268913938922953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6869 = (14869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6870) ≤ val WuPaper.ClassicalFourthData.Bq 6870
    have hp : val WuPaper.ClassicalFourthData.Bq 6870 = (268920602559089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6870 = 268920602559089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6870 = (1487:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6871) ≤ val WuPaper.ClassicalFourthData.Bq 6871
    have hp : val WuPaper.ClassicalFourthData.Bq 6871 = (268927263022570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6871 = 268927263022570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6871 = (14871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6871
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6872) ≤ val WuPaper.ClassicalFourthData.Bq 6872
    have hp : val WuPaper.ClassicalFourthData.Bq 6872 = (268933920314454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6872 = 268933920314454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6872 = (1859:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6873) ≤ val WuPaper.ClassicalFourthData.Bq 6873
    have hp : val WuPaper.ClassicalFourthData.Bq 6873 = (268940574435799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6873 = 268940574435799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6873 = (14873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6874) ≤ val WuPaper.ClassicalFourthData.Bq 6874
    have hp : val WuPaper.ClassicalFourthData.Bq 6874 = (268947225387664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6874 = 268947225387664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6874 = (7437:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6875) ≤ val WuPaper.ClassicalFourthData.Bq 6875
    have hp : val WuPaper.ClassicalFourthData.Bq 6875 = (268953873171105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6875 = 268953873171105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6875 = (119:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6876) ≤ val WuPaper.ClassicalFourthData.Bq 6876
    have hp : val WuPaper.ClassicalFourthData.Bq 6876 = (268960517787180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6876 = 268960517787180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6876 = (3719:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6877) ≤ val WuPaper.ClassicalFourthData.Bq 6877
    have hp : val WuPaper.ClassicalFourthData.Bq 6877 = (268967159236946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6877 = 268967159236946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6877 = (14877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6878) ≤ val WuPaper.ClassicalFourthData.Bq 6878
    have hp : val WuPaper.ClassicalFourthData.Bq 6878 = (268973797521460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6878 = 268973797521460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6878 = (7439:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6879) ≤ val WuPaper.ClassicalFourthData.Bq 6879
    have hp : val WuPaper.ClassicalFourthData.Bq 6879 = (268980432641776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6879 = 268980432641776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6879 = (14879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_429
