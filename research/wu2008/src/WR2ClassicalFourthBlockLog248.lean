import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints248
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_248 (j : Fin 16) (hj : 16*248+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*248+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*248+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3968) ≤ val WuPaper.ClassicalFourthData.Bq 3968
    have hp : val WuPaper.ClassicalFourthData.Bq 3968 = (230327259078345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3968 = 230327259078345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3968 = (374:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3969) ≤ val WuPaper.ClassicalFourthData.Bq 3969
    have hp : val WuPaper.ClassicalFourthData.Bq 3969 = (230349955149377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3969 = 230349955149377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3969 = (11969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3970) ≤ val WuPaper.ClassicalFourthData.Bq 3970
    have hp : val WuPaper.ClassicalFourthData.Bq 3970 = (230372642166160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3970 = 230372642166160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3970 = (1197:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3971) ≤ val WuPaper.ClassicalFourthData.Bq 3971
    have hp : val WuPaper.ClassicalFourthData.Bq 3971 = (230395320132285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3971 = 230395320132285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3971 = (11971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3972) ≤ val WuPaper.ClassicalFourthData.Bq 3972
    have hp : val WuPaper.ClassicalFourthData.Bq 3972 = (230417989051340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3972 = 230417989051340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3972 = (2993:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3973) ≤ val WuPaper.ClassicalFourthData.Bq 3973
    have hp : val WuPaper.ClassicalFourthData.Bq 3973 = (230440648926909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3973 = 230440648926909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3973 = (11973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3974) ≤ val WuPaper.ClassicalFourthData.Bq 3974
    have hp : val WuPaper.ClassicalFourthData.Bq 3974 = (230463299762577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3974 = 230463299762577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3974 = (5987:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3975) ≤ val WuPaper.ClassicalFourthData.Bq 3975
    have hp : val WuPaper.ClassicalFourthData.Bq 3975 = (230485941561927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3975 = 230485941561927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3975 = (479:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3975
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3976) ≤ val WuPaper.ClassicalFourthData.Bq 3976
    have hp : val WuPaper.ClassicalFourthData.Bq 3976 = (230508574328540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3976 = 230508574328540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3976 = (1497:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3977) ≤ val WuPaper.ClassicalFourthData.Bq 3977
    have hp : val WuPaper.ClassicalFourthData.Bq 3977 = (230531198065994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3977 = 230531198065994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3977 = (11977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3978) ≤ val WuPaper.ClassicalFourthData.Bq 3978
    have hp : val WuPaper.ClassicalFourthData.Bq 3978 = (230553812777868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3978 = 230553812777868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3978 = (5989:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3979) ≤ val WuPaper.ClassicalFourthData.Bq 3979
    have hp : val WuPaper.ClassicalFourthData.Bq 3979 = (230576418467737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3979 = 230576418467737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3979 = (11979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3980) ≤ val WuPaper.ClassicalFourthData.Bq 3980
    have hp : val WuPaper.ClassicalFourthData.Bq 3980 = (230599015139175:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3980 = 230599015139175 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3980 = (599:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3981) ≤ val WuPaper.ClassicalFourthData.Bq 3981
    have hp : val WuPaper.ClassicalFourthData.Bq 3981 = (230621602795754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3981 = 230621602795754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3981 = (11981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3982) ≤ val WuPaper.ClassicalFourthData.Bq 3982
    have hp : val WuPaper.ClassicalFourthData.Bq 3982 = (230644181441046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3982 = 230644181441046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3982 = (5991:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3983) ≤ val WuPaper.ClassicalFourthData.Bq 3983
    have hp : val WuPaper.ClassicalFourthData.Bq 3983 = (230666751078619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3983 = 230666751078619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3983 = (11983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_248
