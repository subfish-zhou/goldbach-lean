import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints424
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_424 (j : Fin 16) (hj : 16*424+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*424+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*424+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6784) ≤ val WuPaper.ClassicalFourthData.Bq 6784
    have hp : val WuPaper.ClassicalFourthData.Bq 6784 = (268335820630468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6784 = 268335820630468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6784 = (462:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6785) ≤ val WuPaper.ClassicalFourthData.Bq 6785
    have hp : val WuPaper.ClassicalFourthData.Bq 6785 = (268342757854956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6785 = 268342757854956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6785 = (2957:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6786) ≤ val WuPaper.ClassicalFourthData.Bq 6786
    have hp : val WuPaper.ClassicalFourthData.Bq 6786 = (268349691815310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6786 = 268349691815310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6786 = (7393:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6787) ≤ val WuPaper.ClassicalFourthData.Bq 6787
    have hp : val WuPaper.ClassicalFourthData.Bq 6787 = (268356622512627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6787 = 268356622512627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6787 = (14787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6788) ≤ val WuPaper.ClassicalFourthData.Bq 6788
    have hp : val WuPaper.ClassicalFourthData.Bq 6788 = (268363549947997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6788 = 268363549947997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6788 = (3697:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6789) ≤ val WuPaper.ClassicalFourthData.Bq 6789
    have hp : val WuPaper.ClassicalFourthData.Bq 6789 = (268370474122514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6789 = 268370474122514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6789 = (14789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6790) ≤ val WuPaper.ClassicalFourthData.Bq 6790
    have hp : val WuPaper.ClassicalFourthData.Bq 6790 = (268377395037270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6790 = 268377395037270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6790 = (1479:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6791) ≤ val WuPaper.ClassicalFourthData.Bq 6791
    have hp : val WuPaper.ClassicalFourthData.Bq 6791 = (268384312693356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6791 = 268384312693356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6791 = (14791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6791
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6792) ≤ val WuPaper.ClassicalFourthData.Bq 6792
    have hp : val WuPaper.ClassicalFourthData.Bq 6792 = (268391227091865:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6792 = 268391227091865 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6792 = (1849:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6793) ≤ val WuPaper.ClassicalFourthData.Bq 6793
    have hp : val WuPaper.ClassicalFourthData.Bq 6793 = (268398138233887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6793 = 268398138233887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6793 = (14793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6794) ≤ val WuPaper.ClassicalFourthData.Bq 6794
    have hp : val WuPaper.ClassicalFourthData.Bq 6794 = (268405046120512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6794 = 268405046120512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6794 = (7397:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6795) ≤ val WuPaper.ClassicalFourthData.Bq 6795
    have hp : val WuPaper.ClassicalFourthData.Bq 6795 = (268411950752831:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6795 = 268411950752831 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6795 = (2959:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6796) ≤ val WuPaper.ClassicalFourthData.Bq 6796
    have hp : val WuPaper.ClassicalFourthData.Bq 6796 = (268418852131934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6796 = 268418852131934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6796 = (3699:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6797) ≤ val WuPaper.ClassicalFourthData.Bq 6797
    have hp : val WuPaper.ClassicalFourthData.Bq 6797 = (268425750258909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6797 = 268425750258909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6797 = (14797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6798) ≤ val WuPaper.ClassicalFourthData.Bq 6798
    have hp : val WuPaper.ClassicalFourthData.Bq 6798 = (268432645134845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6798 = 268432645134845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6798 = (7399:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6799) ≤ val WuPaper.ClassicalFourthData.Bq 6799
    have hp : val WuPaper.ClassicalFourthData.Bq 6799 = (268439536760832:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6799 = 268439536760832 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6799 = (14799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_424
