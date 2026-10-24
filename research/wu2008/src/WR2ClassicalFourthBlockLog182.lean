import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints182
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_182 (j : Fin 16) (hj : 16*182+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*182+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*182+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2912) ≤ val WuPaper.ClassicalFourthData.Bq 2912
    have hp : val WuPaper.ClassicalFourthData.Bq 2912 = (200500245741153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2912 = 200500245741153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2912 = (341:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2913) ≤ val WuPaper.ClassicalFourthData.Bq 2913
    have hp : val WuPaper.ClassicalFourthData.Bq 2913 = (200534898137355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2913 = 200534898137355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2913 = (10913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2914) ≤ val WuPaper.ClassicalFourthData.Bq 2914
    have hp : val WuPaper.ClassicalFourthData.Bq 2914 = (200569536514401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2914 = 200569536514401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2914 = (5457:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2915) ≤ val WuPaper.ClassicalFourthData.Bq 2915
    have hp : val WuPaper.ClassicalFourthData.Bq 2915 = (200604160878363:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2915 = 200604160878363 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2915 = (2183:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2916) ≤ val WuPaper.ClassicalFourthData.Bq 2916
    have hp : val WuPaper.ClassicalFourthData.Bq 2916 = (200638771235308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2916 = 200638771235308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2916 = (2729:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2917) ≤ val WuPaper.ClassicalFourthData.Bq 2917
    have hp : val WuPaper.ClassicalFourthData.Bq 2917 = (200673367591301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2917 = 200673367591301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2917 = (10917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2918) ≤ val WuPaper.ClassicalFourthData.Bq 2918
    have hp : val WuPaper.ClassicalFourthData.Bq 2918 = (200707949952404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2918 = 200707949952404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2918 = (5459:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2919) ≤ val WuPaper.ClassicalFourthData.Bq 2919
    have hp : val WuPaper.ClassicalFourthData.Bq 2919 = (200742518324676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2919 = 200742518324676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2919 = (10919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2919
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2920) ≤ val WuPaper.ClassicalFourthData.Bq 2920
    have hp : val WuPaper.ClassicalFourthData.Bq 2920 = (200777072714172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2920 = 200777072714172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2920 = (273:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2921) ≤ val WuPaper.ClassicalFourthData.Bq 2921
    have hp : val WuPaper.ClassicalFourthData.Bq 2921 = (200811613126943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2921 = 200811613126943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2921 = (10921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2922) ≤ val WuPaper.ClassicalFourthData.Bq 2922
    have hp : val WuPaper.ClassicalFourthData.Bq 2922 = (200846139569040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2922 = 200846139569040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2922 = (5461:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2923) ≤ val WuPaper.ClassicalFourthData.Bq 2923
    have hp : val WuPaper.ClassicalFourthData.Bq 2923 = (200880652046507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2923 = 200880652046507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2923 = (10923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2924) ≤ val WuPaper.ClassicalFourthData.Bq 2924
    have hp : val WuPaper.ClassicalFourthData.Bq 2924 = (200915150565388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2924 = 200915150565388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2924 = (2731:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2925) ≤ val WuPaper.ClassicalFourthData.Bq 2925
    have hp : val WuPaper.ClassicalFourthData.Bq 2925 = (200949635131721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2925 = 200949635131721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2925 = (437:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2926) ≤ val WuPaper.ClassicalFourthData.Bq 2926
    have hp : val WuPaper.ClassicalFourthData.Bq 2926 = (200984105751543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2926 = 200984105751543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2926 = (5463:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2927) ≤ val WuPaper.ClassicalFourthData.Bq 2927
    have hp : val WuPaper.ClassicalFourthData.Bq 2927 = (201018562430888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2927 = 201018562430888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2927 = (10927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_182
