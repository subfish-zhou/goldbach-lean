import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints051
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_051 (j : Fin 16) (hj : 16*51+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*51+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*51+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 816) ≤ val WuPaper.ClassicalFourthData.Bq 816
    have hp : val WuPaper.ClassicalFourthData.Bq 816 = (84232916010268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 816 = 84232916010268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 816 = (551:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 817) ≤ val WuPaper.ClassicalFourthData.Bq 817
    have hp : val WuPaper.ClassicalFourthData.Bq 817 = (84317553148778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 817 = 84317553148778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 817 = (8817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 818) ≤ val WuPaper.ClassicalFourthData.Bq 818
    have hp : val WuPaper.ClassicalFourthData.Bq 818 = (84402151541297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 818 = 84402151541297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 818 = (4409:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 819) ≤ val WuPaper.ClassicalFourthData.Bq 819
    have hp : val WuPaper.ClassicalFourthData.Bq 819 = (84486711209119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 819 = 84486711209119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 819 = (8819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 820) ≤ val WuPaper.ClassicalFourthData.Bq 820
    have hp : val WuPaper.ClassicalFourthData.Bq 820 = (84571232173524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 820 = 84571232173524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 820 = (441:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 821) ≤ val WuPaper.ClassicalFourthData.Bq 821
    have hp : val WuPaper.ClassicalFourthData.Bq 821 = (84655714455774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 821 = 84655714455774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 821 = (8821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 822) ≤ val WuPaper.ClassicalFourthData.Bq 822
    have hp : val WuPaper.ClassicalFourthData.Bq 822 = (84740158077121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 822 = 84740158077121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 822 = (4411:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 823) ≤ val WuPaper.ClassicalFourthData.Bq 823
    have hp : val WuPaper.ClassicalFourthData.Bq 823 = (84824563058799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 823 = 84824563058799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 823 = (8823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_823
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 824) ≤ val WuPaper.ClassicalFourthData.Bq 824
    have hp : val WuPaper.ClassicalFourthData.Bq 824 = (84908929422028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 824 = 84908929422028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 824 = (1103:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 825) ≤ val WuPaper.ClassicalFourthData.Bq 825
    have hp : val WuPaper.ClassicalFourthData.Bq 825 = (84993257188016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 825 = 84993257188016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 825 = (353:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 826) ≤ val WuPaper.ClassicalFourthData.Bq 826
    have hp : val WuPaper.ClassicalFourthData.Bq 826 = (85077546377952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 826 = 85077546377952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 826 = (4413:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 827) ≤ val WuPaper.ClassicalFourthData.Bq 827
    have hp : val WuPaper.ClassicalFourthData.Bq 827 = (85161797013013:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 827 = 85161797013013 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 827 = (8827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 828) ≤ val WuPaper.ClassicalFourthData.Bq 828
    have hp : val WuPaper.ClassicalFourthData.Bq 828 = (85246009114361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 828 = 85246009114361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 828 = (2207:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 829) ≤ val WuPaper.ClassicalFourthData.Bq 829
    have hp : val WuPaper.ClassicalFourthData.Bq 829 = (85330182703144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 829 = 85330182703144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 829 = (8829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 830) ≤ val WuPaper.ClassicalFourthData.Bq 830
    have hp : val WuPaper.ClassicalFourthData.Bq 830 = (85414317800495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 830 = 85414317800495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 830 = (883:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 831) ≤ val WuPaper.ClassicalFourthData.Bq 831
    have hp : val WuPaper.ClassicalFourthData.Bq 831 = (85498414427530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 831 = 85498414427530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 831 = (8831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_051
