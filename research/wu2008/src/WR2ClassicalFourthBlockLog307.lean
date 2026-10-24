import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints307
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_307 (j : Fin 16) (hj : 16*307+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*307+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*307+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4912) ≤ val WuPaper.ClassicalFourthData.Bq 4912
    have hp : val WuPaper.ClassicalFourthData.Bq 4912 = (248173581804535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4912 = 248173581804535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4912 = (807:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4913) ≤ val WuPaper.ClassicalFourthData.Bq 4913
    have hp : val WuPaper.ClassicalFourthData.Bq 4913 = (248189119191107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4913 = 248189119191107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4913 = (12913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4914) ≤ val WuPaper.ClassicalFourthData.Bq 4914
    have hp : val WuPaper.ClassicalFourthData.Bq 4914 = (248204650272410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4914 = 248204650272410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4914 = (6457:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4915) ≤ val WuPaper.ClassicalFourthData.Bq 4915
    have hp : val WuPaper.ClassicalFourthData.Bq 4915 = (248220175050783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4915 = 248220175050783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4915 = (2583:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4916) ≤ val WuPaper.ClassicalFourthData.Bq 4916
    have hp : val WuPaper.ClassicalFourthData.Bq 4916 = (248235693528564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4916 = 248235693528564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4916 = (3229:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4917) ≤ val WuPaper.ClassicalFourthData.Bq 4917
    have hp : val WuPaper.ClassicalFourthData.Bq 4917 = (248251205708091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4917 = 248251205708091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4917 = (12917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4918) ≤ val WuPaper.ClassicalFourthData.Bq 4918
    have hp : val WuPaper.ClassicalFourthData.Bq 4918 = (248266711591700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4918 = 248266711591700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4918 = (6459:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4919) ≤ val WuPaper.ClassicalFourthData.Bq 4919
    have hp : val WuPaper.ClassicalFourthData.Bq 4919 = (248282211181727:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4919 = 248282211181727 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4919 = (12919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4919
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4920) ≤ val WuPaper.ClassicalFourthData.Bq 4920
    have hp : val WuPaper.ClassicalFourthData.Bq 4920 = (248297704480504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4920 = 248297704480504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4920 = (323:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4921) ≤ val WuPaper.ClassicalFourthData.Bq 4921
    have hp : val WuPaper.ClassicalFourthData.Bq 4921 = (248313191490367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4921 = 248313191490367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4921 = (12921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4922) ≤ val WuPaper.ClassicalFourthData.Bq 4922
    have hp : val WuPaper.ClassicalFourthData.Bq 4922 = (248328672213646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4922 = 248328672213646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4922 = (6461:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4923) ≤ val WuPaper.ClassicalFourthData.Bq 4923
    have hp : val WuPaper.ClassicalFourthData.Bq 4923 = (248344146652674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4923 = 248344146652674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4923 = (12923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4924) ≤ val WuPaper.ClassicalFourthData.Bq 4924
    have hp : val WuPaper.ClassicalFourthData.Bq 4924 = (248359614809779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4924 = 248359614809779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4924 = (3231:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4925) ≤ val WuPaper.ClassicalFourthData.Bq 4925
    have hp : val WuPaper.ClassicalFourthData.Bq 4925 = (248375076687293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4925 = 248375076687293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4925 = (517:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4926) ≤ val WuPaper.ClassicalFourthData.Bq 4926
    have hp : val WuPaper.ClassicalFourthData.Bq 4926 = (248390532287541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4926 = 248390532287541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4926 = (6463:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4927) ≤ val WuPaper.ClassicalFourthData.Bq 4927
    have hp : val WuPaper.ClassicalFourthData.Bq 4927 = (248405981612853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4927 = 248405981612853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4927 = (12927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_307
