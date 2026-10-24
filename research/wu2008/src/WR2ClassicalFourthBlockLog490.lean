import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints490
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_490 (j : Fin 16) (hj : 16*490+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*490+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*490+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7840) ≤ val WuPaper.ClassicalFourthData.Bq 7840
    have hp : val WuPaper.ClassicalFourthData.Bq 7840 = (274037694024693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7840 = 274037694024693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7840 = (99:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7841) ≤ val WuPaper.ClassicalFourthData.Bq 7841
    have hp : val WuPaper.ClassicalFourthData.Bq 7841 = (274041720656713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7841 = 274041720656713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7841 = (15841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7842) ≤ val WuPaper.ClassicalFourthData.Bq 7842
    have hp : val WuPaper.ClassicalFourthData.Bq 7842 = (274045744979552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7842 = 274045744979552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7842 = (7921:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7843) ≤ val WuPaper.ClassicalFourthData.Bq 7843
    have hp : val WuPaper.ClassicalFourthData.Bq 7843 = (274049766993952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7843 = 274049766993952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7843 = (15843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7844) ≤ val WuPaper.ClassicalFourthData.Bq 7844
    have hp : val WuPaper.ClassicalFourthData.Bq 7844 = (274053786700653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7844 = 274053786700653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7844 = (3961:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7845) ≤ val WuPaper.ClassicalFourthData.Bq 7845
    have hp : val WuPaper.ClassicalFourthData.Bq 7845 = (274057804100396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7845 = 274057804100396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7845 = (3169:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7846) ≤ val WuPaper.ClassicalFourthData.Bq 7846
    have hp : val WuPaper.ClassicalFourthData.Bq 7846 = (274061819193922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7846 = 274061819193922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7846 = (7923:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7847) ≤ val WuPaper.ClassicalFourthData.Bq 7847
    have hp : val WuPaper.ClassicalFourthData.Bq 7847 = (274065831981971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7847 = 274065831981971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7847 = (15847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7847
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7848) ≤ val WuPaper.ClassicalFourthData.Bq 7848
    have hp : val WuPaper.ClassicalFourthData.Bq 7848 = (274069842465284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7848 = 274069842465284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7848 = (1981:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7849) ≤ val WuPaper.ClassicalFourthData.Bq 7849
    have hp : val WuPaper.ClassicalFourthData.Bq 7849 = (274073850644599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7849 = 274073850644599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7849 = (15849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7850) ≤ val WuPaper.ClassicalFourthData.Bq 7850
    have hp : val WuPaper.ClassicalFourthData.Bq 7850 = (274077856520657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7850 = 274077856520657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7850 = (317:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7851) ≤ val WuPaper.ClassicalFourthData.Bq 7851
    have hp : val WuPaper.ClassicalFourthData.Bq 7851 = (274081860094197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7851 = 274081860094197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7851 = (15851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7852) ≤ val WuPaper.ClassicalFourthData.Bq 7852
    have hp : val WuPaper.ClassicalFourthData.Bq 7852 = (274085861365958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7852 = 274085861365958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7852 = (3963:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7853) ≤ val WuPaper.ClassicalFourthData.Bq 7853
    have hp : val WuPaper.ClassicalFourthData.Bq 7853 = (274089860336678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7853 = 274089860336678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7853 = (15853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7854) ≤ val WuPaper.ClassicalFourthData.Bq 7854
    have hp : val WuPaper.ClassicalFourthData.Bq 7854 = (274093857007096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7854 = 274093857007096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7854 = (7927:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7855) ≤ val WuPaper.ClassicalFourthData.Bq 7855
    have hp : val WuPaper.ClassicalFourthData.Bq 7855 = (274097851377951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7855 = 274097851377951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7855 = (3171:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_490
