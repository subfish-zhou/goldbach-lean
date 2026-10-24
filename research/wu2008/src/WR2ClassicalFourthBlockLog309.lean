import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints309
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_309 (j : Fin 16) (hj : 16*309+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*309+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*309+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4944) ≤ val WuPaper.ClassicalFourthData.Bq 4944
    have hp : val WuPaper.ClassicalFourthData.Bq 4944 = (248667662327829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4944 = 248667662327829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4944 = (809:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4945) ≤ val WuPaper.ClassicalFourthData.Bq 4945
    have hp : val WuPaper.ClassicalFourthData.Bq 4945 = (248682999101056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4945 = 248682999101056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4945 = (2589:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4946) ≤ val WuPaper.ClassicalFourthData.Bq 4946
    have hp : val WuPaper.ClassicalFourthData.Bq 4946 = (248698329643370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4946 = 248698329643370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4946 = (6473:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4947) ≤ val WuPaper.ClassicalFourthData.Bq 4947
    have hp : val WuPaper.ClassicalFourthData.Bq 4947 = (248713653957077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4947 = 248713653957077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4947 = (12947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4948) ≤ val WuPaper.ClassicalFourthData.Bq 4948
    have hp : val WuPaper.ClassicalFourthData.Bq 4948 = (248728972044484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4948 = 248728972044484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4948 = (3237:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4949) ≤ val WuPaper.ClassicalFourthData.Bq 4949
    have hp : val WuPaper.ClassicalFourthData.Bq 4949 = (248744283907895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4949 = 248744283907895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4949 = (12949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4950) ≤ val WuPaper.ClassicalFourthData.Bq 4950
    have hp : val WuPaper.ClassicalFourthData.Bq 4950 = (248759589549614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4950 = 248759589549614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4950 = (259:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4951) ≤ val WuPaper.ClassicalFourthData.Bq 4951
    have hp : val WuPaper.ClassicalFourthData.Bq 4951 = (248774888971945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4951 = 248774888971945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4951 = (12951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4951
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4952) ≤ val WuPaper.ClassicalFourthData.Bq 4952
    have hp : val WuPaper.ClassicalFourthData.Bq 4952 = (248790182177188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4952 = 248790182177188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4952 = (1619:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4953) ≤ val WuPaper.ClassicalFourthData.Bq 4953
    have hp : val WuPaper.ClassicalFourthData.Bq 4953 = (248805469167646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4953 = 248805469167646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4953 = (12953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4954) ≤ val WuPaper.ClassicalFourthData.Bq 4954
    have hp : val WuPaper.ClassicalFourthData.Bq 4954 = (248820749945618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4954 = 248820749945618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4954 = (6477:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4955) ≤ val WuPaper.ClassicalFourthData.Bq 4955
    have hp : val WuPaper.ClassicalFourthData.Bq 4955 = (248836024513404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4955 = 248836024513404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4955 = (2591:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4956) ≤ val WuPaper.ClassicalFourthData.Bq 4956
    have hp : val WuPaper.ClassicalFourthData.Bq 4956 = (248851292873300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4956 = 248851292873300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4956 = (3239:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4957) ≤ val WuPaper.ClassicalFourthData.Bq 4957
    have hp : val WuPaper.ClassicalFourthData.Bq 4957 = (248866555027605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4957 = 248866555027605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4957 = (12957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4958) ≤ val WuPaper.ClassicalFourthData.Bq 4958
    have hp : val WuPaper.ClassicalFourthData.Bq 4958 = (248881810978614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4958 = 248881810978614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4958 = (6479:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4959) ≤ val WuPaper.ClassicalFourthData.Bq 4959
    have hp : val WuPaper.ClassicalFourthData.Bq 4959 = (248897060728622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4959 = 248897060728622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4959 = (12959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_309
