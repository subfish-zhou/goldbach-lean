import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints192
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_192 (j : Fin 16) (hj : 16*192+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*192+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*192+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3072) ≤ val WuPaper.ClassicalFourthData.Bq 3072
    have hp : val WuPaper.ClassicalFourthData.Bq 3072 = (205870290540265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3072 = 205870290540265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3072 = (346:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3073) ≤ val WuPaper.ClassicalFourthData.Bq 3073
    have hp : val WuPaper.ClassicalFourthData.Bq 3073 = (205902775014527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3073 = 205902775014527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3073 = (11073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3074) ≤ val WuPaper.ClassicalFourthData.Bq 3074
    have hp : val WuPaper.ClassicalFourthData.Bq 3074 = (205935246401806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3074 = 205935246401806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3074 = (5537:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3075) ≤ val WuPaper.ClassicalFourthData.Bq 3075
    have hp : val WuPaper.ClassicalFourthData.Bq 3075 = (205967704707688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3075 = 205967704707688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3075 = (443:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3076) ≤ val WuPaper.ClassicalFourthData.Bq 3076
    have hp : val WuPaper.ClassicalFourthData.Bq 3076 = (206000149937757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3076 = 206000149937757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3076 = (2769:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3077) ≤ val WuPaper.ClassicalFourthData.Bq 3077
    have hp : val WuPaper.ClassicalFourthData.Bq 3077 = (206032582097593:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3077 = 206032582097593 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3077 = (11077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3078) ≤ val WuPaper.ClassicalFourthData.Bq 3078
    have hp : val WuPaper.ClassicalFourthData.Bq 3078 = (206065001192772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3078 = 206065001192772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3078 = (5539:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3079) ≤ val WuPaper.ClassicalFourthData.Bq 3079
    have hp : val WuPaper.ClassicalFourthData.Bq 3079 = (206097407228870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3079 = 206097407228870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3079 = (11079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3079
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3080) ≤ val WuPaper.ClassicalFourthData.Bq 3080
    have hp : val WuPaper.ClassicalFourthData.Bq 3080 = (206129800211458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3080 = 206129800211458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3080 = (277:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3081) ≤ val WuPaper.ClassicalFourthData.Bq 3081
    have hp : val WuPaper.ClassicalFourthData.Bq 3081 = (206162180146105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3081 = 206162180146105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3081 = (11081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3082) ≤ val WuPaper.ClassicalFourthData.Bq 3082
    have hp : val WuPaper.ClassicalFourthData.Bq 3082 = (206194547038377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3082 = 206194547038377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3082 = (5541:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3083) ≤ val WuPaper.ClassicalFourthData.Bq 3083
    have hp : val WuPaper.ClassicalFourthData.Bq 3083 = (206226900893836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3083 = 206226900893836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3083 = (11083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3084) ≤ val WuPaper.ClassicalFourthData.Bq 3084
    have hp : val WuPaper.ClassicalFourthData.Bq 3084 = (206259241718043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3084 = 206259241718043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3084 = (2771:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3085) ≤ val WuPaper.ClassicalFourthData.Bq 3085
    have hp : val WuPaper.ClassicalFourthData.Bq 3085 = (206291569516556:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3085 = 206291569516556 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3085 = (2217:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3086) ≤ val WuPaper.ClassicalFourthData.Bq 3086
    have hp : val WuPaper.ClassicalFourthData.Bq 3086 = (206323884294927:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3086 = 206323884294927 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3086 = (5543:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3087) ≤ val WuPaper.ClassicalFourthData.Bq 3087
    have hp : val WuPaper.ClassicalFourthData.Bq 3087 = (206356186058710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3087 = 206356186058710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3087 = (11087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_192
