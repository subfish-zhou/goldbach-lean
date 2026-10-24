import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints365
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_365 (j : Fin 16) (hj : 16*365+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*365+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*365+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5840) ≤ val WuPaper.ClassicalFourthData.Bq 5840
    have hp : val WuPaper.ClassicalFourthData.Bq 5840 = (260162239868290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5840 = 260162239868290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5840 = (173:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5841) ≤ val WuPaper.ClassicalFourthData.Bq 5841
    have hp : val WuPaper.ClassicalFourthData.Bq 5841 = (260172811443384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5841 = 260172811443384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5841 = (13841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5842) ≤ val WuPaper.ClassicalFourthData.Bq 5842
    have hp : val WuPaper.ClassicalFourthData.Bq 5842 = (260183378507125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5842 = 260183378507125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5842 = (6921:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5843) ≤ val WuPaper.ClassicalFourthData.Bq 5843
    have hp : val WuPaper.ClassicalFourthData.Bq 5843 = (260193941061098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5843 = 260193941061098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5843 = (13843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5844) ≤ val WuPaper.ClassicalFourthData.Bq 5844
    have hp : val WuPaper.ClassicalFourthData.Bq 5844 = (260204499106885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5844 = 260204499106885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5844 = (3461:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5845) ≤ val WuPaper.ClassicalFourthData.Bq 5845
    have hp : val WuPaper.ClassicalFourthData.Bq 5845 = (260215052646070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5845 = 260215052646070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5845 = (2769:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5846) ≤ val WuPaper.ClassicalFourthData.Bq 5846
    have hp : val WuPaper.ClassicalFourthData.Bq 5846 = (260225601680234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5846 = 260225601680234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5846 = (6923:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5847) ≤ val WuPaper.ClassicalFourthData.Bq 5847
    have hp : val WuPaper.ClassicalFourthData.Bq 5847 = (260236146210959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5847 = 260236146210959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5847 = (13847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5847
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5848) ≤ val WuPaper.ClassicalFourthData.Bq 5848
    have hp : val WuPaper.ClassicalFourthData.Bq 5848 = (260246686239825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5848 = 260246686239825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5848 = (1731:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5849) ≤ val WuPaper.ClassicalFourthData.Bq 5849
    have hp : val WuPaper.ClassicalFourthData.Bq 5849 = (260257221768413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5849 = 260257221768413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5849 = (13849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5850) ≤ val WuPaper.ClassicalFourthData.Bq 5850
    have hp : val WuPaper.ClassicalFourthData.Bq 5850 = (260267752798301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5850 = 260267752798301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5850 = (277:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5851) ≤ val WuPaper.ClassicalFourthData.Bq 5851
    have hp : val WuPaper.ClassicalFourthData.Bq 5851 = (260278279331070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5851 = 260278279331070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5851 = (13851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5852) ≤ val WuPaper.ClassicalFourthData.Bq 5852
    have hp : val WuPaper.ClassicalFourthData.Bq 5852 = (260288801368297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5852 = 260288801368297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5852 = (3463:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5853) ≤ val WuPaper.ClassicalFourthData.Bq 5853
    have hp : val WuPaper.ClassicalFourthData.Bq 5853 = (260299318911560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5853 = 260299318911560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5853 = (13853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5854) ≤ val WuPaper.ClassicalFourthData.Bq 5854
    have hp : val WuPaper.ClassicalFourthData.Bq 5854 = (260309831962435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5854 = 260309831962435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5854 = (6927:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5855) ≤ val WuPaper.ClassicalFourthData.Bq 5855
    have hp : val WuPaper.ClassicalFourthData.Bq 5855 = (260320340522499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5855 = 260320340522499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5855 = (2771:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_365
