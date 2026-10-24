import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints295
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_295 (j : Fin 16) (hj : 16*295+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*295+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*295+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4720) ≤ val WuPaper.ClassicalFourthData.Bq 4720
    have hp : val WuPaper.ClassicalFourthData.Bq 4720 = (245070715975157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4720 = 245070715975157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4720 = (159:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4721) ≤ val WuPaper.ClassicalFourthData.Bq 4721
    have hp : val WuPaper.ClassicalFourthData.Bq 4721 = (245087508568496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4721 = 245087508568496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4721 = (12721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4722) ≤ val WuPaper.ClassicalFourthData.Bq 4722
    have hp : val WuPaper.ClassicalFourthData.Bq 4722 = (245104294387891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4722 = 245104294387891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4722 = (6361:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4723) ≤ val WuPaper.ClassicalFourthData.Bq 4723
    have hp : val WuPaper.ClassicalFourthData.Bq 4723 = (245121073435885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4723 = 245121073435885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4723 = (12723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4724) ≤ val WuPaper.ClassicalFourthData.Bq 4724
    have hp : val WuPaper.ClassicalFourthData.Bq 4724 = (245137845715025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4724 = 245137845715025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4724 = (3181:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4725) ≤ val WuPaper.ClassicalFourthData.Bq 4725
    have hp : val WuPaper.ClassicalFourthData.Bq 4725 = (245154611227851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4725 = 245154611227851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4725 = (509:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4726) ≤ val WuPaper.ClassicalFourthData.Bq 4726
    have hp : val WuPaper.ClassicalFourthData.Bq 4726 = (245171369976907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4726 = 245171369976907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4726 = (6363:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4727) ≤ val WuPaper.ClassicalFourthData.Bq 4727
    have hp : val WuPaper.ClassicalFourthData.Bq 4727 = (245188121964732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4727 = 245188121964732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4727 = (12727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4727
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4728) ≤ val WuPaper.ClassicalFourthData.Bq 4728
    have hp : val WuPaper.ClassicalFourthData.Bq 4728 = (245204867193866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4728 = 245204867193866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4728 = (1591:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4729) ≤ val WuPaper.ClassicalFourthData.Bq 4729
    have hp : val WuPaper.ClassicalFourthData.Bq 4729 = (245221605666847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4729 = 245221605666847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4729 = (12729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4730) ≤ val WuPaper.ClassicalFourthData.Bq 4730
    have hp : val WuPaper.ClassicalFourthData.Bq 4730 = (245238337386213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4730 = 245238337386213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4730 = (1273:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4731) ≤ val WuPaper.ClassicalFourthData.Bq 4731
    have hp : val WuPaper.ClassicalFourthData.Bq 4731 = (245255062354499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4731 = 245255062354499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4731 = (12731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4732) ≤ val WuPaper.ClassicalFourthData.Bq 4732
    have hp : val WuPaper.ClassicalFourthData.Bq 4732 = (245271780574241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4732 = 245271780574241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4732 = (3183:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4733) ≤ val WuPaper.ClassicalFourthData.Bq 4733
    have hp : val WuPaper.ClassicalFourthData.Bq 4733 = (245288492047972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4733 = 245288492047972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4733 = (12733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4734) ≤ val WuPaper.ClassicalFourthData.Bq 4734
    have hp : val WuPaper.ClassicalFourthData.Bq 4734 = (245305196778225:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4734 = 245305196778225 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4734 = (6367:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4735) ≤ val WuPaper.ClassicalFourthData.Bq 4735
    have hp : val WuPaper.ClassicalFourthData.Bq 4735 = (245321894767532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4735 = 245321894767532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4735 = (2547:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_295
