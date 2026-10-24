import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints431
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_431 (j : Fin 16) (hj : 16*431+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*431+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*431+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6896) ≤ val WuPaper.ClassicalFourthData.Bq 6896
    have hp : val WuPaper.ClassicalFourthData.Bq 6896 = (269092746586323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6896 = 269092746586323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6896 = (931:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6897) ≤ val WuPaper.ClassicalFourthData.Bq 6897
    have hp : val WuPaper.ClassicalFourthData.Bq 6897 = (269099324931210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6897 = 269099324931210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6897 = (14897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6898) ≤ val WuPaper.ClassicalFourthData.Bq 6898
    have hp : val WuPaper.ClassicalFourthData.Bq 6898 = (269105900131888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6898 = 269105900131888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6898 = (7449:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6899) ≤ val WuPaper.ClassicalFourthData.Bq 6899
    have hp : val WuPaper.ClassicalFourthData.Bq 6899 = (269112472189405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6899 = 269112472189405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6899 = (14899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6900) ≤ val WuPaper.ClassicalFourthData.Bq 6900
    have hp : val WuPaper.ClassicalFourthData.Bq 6900 = (269119041104808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6900 = 269119041104808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6900 = (149:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6901) ≤ val WuPaper.ClassicalFourthData.Bq 6901
    have hp : val WuPaper.ClassicalFourthData.Bq 6901 = (269125606879144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6901 = 269125606879144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6901 = (14901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6902) ≤ val WuPaper.ClassicalFourthData.Bq 6902
    have hp : val WuPaper.ClassicalFourthData.Bq 6902 = (269132169513462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6902 = 269132169513462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6902 = (7451:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6903) ≤ val WuPaper.ClassicalFourthData.Bq 6903
    have hp : val WuPaper.ClassicalFourthData.Bq 6903 = (269138729008805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6903 = 269138729008805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6903 = (14903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6903
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6904) ≤ val WuPaper.ClassicalFourthData.Bq 6904
    have hp : val WuPaper.ClassicalFourthData.Bq 6904 = (269145285366222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6904 = 269145285366222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6904 = (1863:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6905) ≤ val WuPaper.ClassicalFourthData.Bq 6905
    have hp : val WuPaper.ClassicalFourthData.Bq 6905 = (269151838586758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6905 = 269151838586758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6905 = (2981:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6906) ≤ val WuPaper.ClassicalFourthData.Bq 6906
    have hp : val WuPaper.ClassicalFourthData.Bq 6906 = (269158388671457:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6906 = 269158388671457 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6906 = (7453:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6907) ≤ val WuPaper.ClassicalFourthData.Bq 6907
    have hp : val WuPaper.ClassicalFourthData.Bq 6907 = (269164935621365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6907 = 269164935621365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6907 = (14907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6908) ≤ val WuPaper.ClassicalFourthData.Bq 6908
    have hp : val WuPaper.ClassicalFourthData.Bq 6908 = (269171479437525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6908 = 269171479437525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6908 = (3727:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6909) ≤ val WuPaper.ClassicalFourthData.Bq 6909
    have hp : val WuPaper.ClassicalFourthData.Bq 6909 = (269178020120983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6909 = 269178020120983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6909 = (14909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6910) ≤ val WuPaper.ClassicalFourthData.Bq 6910
    have hp : val WuPaper.ClassicalFourthData.Bq 6910 = (269184557672782:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6910 = 269184557672782 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6910 = (1491:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6911) ≤ val WuPaper.ClassicalFourthData.Bq 6911
    have hp : val WuPaper.ClassicalFourthData.Bq 6911 = (269191092093965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6911 = 269191092093965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6911 = (14911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_431
