import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints056
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_056 (j : Fin 16) (hj : 16*56+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*56+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*56+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 896) ≤ val WuPaper.ClassicalFourthData.Bq 896
    have hp : val WuPaper.ClassicalFourthData.Bq 896 = (90883176299521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 896 = 90883176299521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 896 = (278:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 897) ≤ val WuPaper.ClassicalFourthData.Bq 897
    have hp : val WuPaper.ClassicalFourthData.Bq 897 = (90964779858510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 897 = 90964779858510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 897 = (8897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 898) ≤ val WuPaper.ClassicalFourthData.Bq 898
    have hp : val WuPaper.ClassicalFourthData.Bq 898 = (91046346329551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 898 = 91046346329551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 898 = (4449:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 899) ≤ val WuPaper.ClassicalFourthData.Bq 899
    have hp : val WuPaper.ClassicalFourthData.Bq 899 = (91127875732801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 899 = 91127875732801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 899 = (8899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 900) ≤ val WuPaper.ClassicalFourthData.Bq 900
    have hp : val WuPaper.ClassicalFourthData.Bq 900 = (91209368088401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 900 = 91209368088401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 900 = (89:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 901) ≤ val WuPaper.ClassicalFourthData.Bq 901
    have hp : val WuPaper.ClassicalFourthData.Bq 901 = (91290823416479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 901 = 91290823416479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 901 = (8901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 902) ≤ val WuPaper.ClassicalFourthData.Bq 902
    have hp : val WuPaper.ClassicalFourthData.Bq 902 = (91372241737152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 902 = 91372241737152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 902 = (4451:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 903) ≤ val WuPaper.ClassicalFourthData.Bq 903
    have hp : val WuPaper.ClassicalFourthData.Bq 903 = (91453623070519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 903 = 91453623070519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 903 = (8903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_903
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 904) ≤ val WuPaper.ClassicalFourthData.Bq 904
    have hp : val WuPaper.ClassicalFourthData.Bq 904 = (91534967436667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 904 = 91534967436667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 904 = (1113:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 905) ≤ val WuPaper.ClassicalFourthData.Bq 905
    have hp : val WuPaper.ClassicalFourthData.Bq 905 = (91616274855671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 905 = 91616274855671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 905 = (1781:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 906) ≤ val WuPaper.ClassicalFourthData.Bq 906
    have hp : val WuPaper.ClassicalFourthData.Bq 906 = (91697545347590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 906 = 91697545347590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 906 = (4453:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 907) ≤ val WuPaper.ClassicalFourthData.Bq 907
    have hp : val WuPaper.ClassicalFourthData.Bq 907 = (91778778932470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 907 = 91778778932470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 907 = (8907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 908) ≤ val WuPaper.ClassicalFourthData.Bq 908
    have hp : val WuPaper.ClassicalFourthData.Bq 908 = (91859975630344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 908 = 91859975630344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 908 = (2227:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 909) ≤ val WuPaper.ClassicalFourthData.Bq 909
    have hp : val WuPaper.ClassicalFourthData.Bq 909 = (91941135461231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 909 = 91941135461231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 909 = (8909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 910) ≤ val WuPaper.ClassicalFourthData.Bq 910
    have hp : val WuPaper.ClassicalFourthData.Bq 910 = (92022258445136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 910 = 92022258445136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 910 = (891:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 911) ≤ val WuPaper.ClassicalFourthData.Bq 911
    have hp : val WuPaper.ClassicalFourthData.Bq 911 = (92103344602051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 911 = 92103344602051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 911 = (8911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_056
