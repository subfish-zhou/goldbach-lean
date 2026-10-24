import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints369
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_369 (j : Fin 16) (hj : 16*369+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*369+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*369+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5904) ≤ val WuPaper.ClassicalFourthData.Bq 5904
    have hp : val WuPaper.ClassicalFourthData.Bq 5904 = (260829791375824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5904 = 260829791375824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5904 = (869:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5905) ≤ val WuPaper.ClassicalFourthData.Bq 5905
    have hp : val WuPaper.ClassicalFourthData.Bq 5905 = (260840077391050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5905 = 260840077391050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5905 = (2781:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5906) ≤ val WuPaper.ClassicalFourthData.Bq 5906
    have hp : val WuPaper.ClassicalFourthData.Bq 5906 = (260850358995015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5906 = 260850358995015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5906 = (6953:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5907) ≤ val WuPaper.ClassicalFourthData.Bq 5907
    have hp : val WuPaper.ClassicalFourthData.Bq 5907 = (260860636189262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5907 = 260860636189262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5907 = (13907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5908) ≤ val WuPaper.ClassicalFourthData.Bq 5908
    have hp : val WuPaper.ClassicalFourthData.Bq 5908 = (260870908975334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5908 = 260870908975334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5908 = (3477:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5909) ≤ val WuPaper.ClassicalFourthData.Bq 5909
    have hp : val WuPaper.ClassicalFourthData.Bq 5909 = (260881177354773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5909 = 260881177354773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5909 = (13909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5910) ≤ val WuPaper.ClassicalFourthData.Bq 5910
    have hp : val WuPaper.ClassicalFourthData.Bq 5910 = (260891441329122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5910 = 260891441329122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5910 = (1391:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5911) ≤ val WuPaper.ClassicalFourthData.Bq 5911
    have hp : val WuPaper.ClassicalFourthData.Bq 5911 = (260901700899919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5911 = 260901700899919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5911 = (13911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5911
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5912) ≤ val WuPaper.ClassicalFourthData.Bq 5912
    have hp : val WuPaper.ClassicalFourthData.Bq 5912 = (260911956068708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5912 = 260911956068708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5912 = (1739:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5913) ≤ val WuPaper.ClassicalFourthData.Bq 5913
    have hp : val WuPaper.ClassicalFourthData.Bq 5913 = (260922206837026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5913 = 260922206837026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5913 = (13913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5914) ≤ val WuPaper.ClassicalFourthData.Bq 5914
    have hp : val WuPaper.ClassicalFourthData.Bq 5914 = (260932453206412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5914 = 260932453206412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5914 = (6957:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5915) ≤ val WuPaper.ClassicalFourthData.Bq 5915
    have hp : val WuPaper.ClassicalFourthData.Bq 5915 = (260942695178407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5915 = 260942695178407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5915 = (2783:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5916) ≤ val WuPaper.ClassicalFourthData.Bq 5916
    have hp : val WuPaper.ClassicalFourthData.Bq 5916 = (260952932754547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5916 = 260952932754547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5916 = (3479:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5917) ≤ val WuPaper.ClassicalFourthData.Bq 5917
    have hp : val WuPaper.ClassicalFourthData.Bq 5917 = (260963165936369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5917 = 260963165936369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5917 = (13917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5918) ≤ val WuPaper.ClassicalFourthData.Bq 5918
    have hp : val WuPaper.ClassicalFourthData.Bq 5918 = (260973394725411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5918 = 260973394725411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5918 = (6959:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5919) ≤ val WuPaper.ClassicalFourthData.Bq 5919
    have hp : val WuPaper.ClassicalFourthData.Bq 5919 = (260983619123207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5919 = 260983619123207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5919 = (13919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_369
