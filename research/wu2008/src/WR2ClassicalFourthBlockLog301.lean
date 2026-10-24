import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints301
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_301 (j : Fin 16) (hj : 16*301+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*301+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*301+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4816) ≤ val WuPaper.ClassicalFourthData.Bq 4816
    have hp : val WuPaper.ClassicalFourthData.Bq 4816 = (246652275683730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4816 = 246652275683730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4816 = (801:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4817) ≤ val WuPaper.ClassicalFourthData.Bq 4817
    have hp : val WuPaper.ClassicalFourthData.Bq 4817 = (246668429424983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4817 = 246668429424983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4817 = (12817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4818) ≤ val WuPaper.ClassicalFourthData.Bq 4818
    have hp : val WuPaper.ClassicalFourthData.Bq 4818 = (246684576631567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4818 = 246684576631567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4818 = (6409:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4819) ≤ val WuPaper.ClassicalFourthData.Bq 4819
    have hp : val WuPaper.ClassicalFourthData.Bq 4819 = (246700717305922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4819 = 246700717305922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4819 = (12819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4820) ≤ val WuPaper.ClassicalFourthData.Bq 4820
    have hp : val WuPaper.ClassicalFourthData.Bq 4820 = (246716851450487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4820 = 246716851450487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4820 = (641:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4821) ≤ val WuPaper.ClassicalFourthData.Bq 4821
    have hp : val WuPaper.ClassicalFourthData.Bq 4821 = (246732979067699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4821 = 246732979067699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4821 = (12821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4822) ≤ val WuPaper.ClassicalFourthData.Bq 4822
    have hp : val WuPaper.ClassicalFourthData.Bq 4822 = (246749100159994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4822 = 246749100159994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4822 = (6411:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4823) ≤ val WuPaper.ClassicalFourthData.Bq 4823
    have hp : val WuPaper.ClassicalFourthData.Bq 4823 = (246765214729807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4823 = 246765214729807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4823 = (12823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4823
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4824) ≤ val WuPaper.ClassicalFourthData.Bq 4824
    have hp : val WuPaper.ClassicalFourthData.Bq 4824 = (246781322779573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4824 = 246781322779573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4824 = (1603:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4825) ≤ val WuPaper.ClassicalFourthData.Bq 4825
    have hp : val WuPaper.ClassicalFourthData.Bq 4825 = (246797424311726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4825 = 246797424311726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4825 = (513:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4826) ≤ val WuPaper.ClassicalFourthData.Bq 4826
    have hp : val WuPaper.ClassicalFourthData.Bq 4826 = (246813519328697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4826 = 246813519328697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4826 = (6413:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4827) ≤ val WuPaper.ClassicalFourthData.Bq 4827
    have hp : val WuPaper.ClassicalFourthData.Bq 4827 = (246829607832917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4827 = 246829607832917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4827 = (12827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4828) ≤ val WuPaper.ClassicalFourthData.Bq 4828
    have hp : val WuPaper.ClassicalFourthData.Bq 4828 = (246845689826817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4828 = 246845689826817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4828 = (3207:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4829) ≤ val WuPaper.ClassicalFourthData.Bq 4829
    have hp : val WuPaper.ClassicalFourthData.Bq 4829 = (246861765312825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4829 = 246861765312825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4829 = (12829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4830) ≤ val WuPaper.ClassicalFourthData.Bq 4830
    have hp : val WuPaper.ClassicalFourthData.Bq 4830 = (246877834293369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4830 = 246877834293369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4830 = (1283:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4831) ≤ val WuPaper.ClassicalFourthData.Bq 4831
    have hp : val WuPaper.ClassicalFourthData.Bq 4831 = (246893896770876:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4831 = 246893896770876 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4831 = (12831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_301
