import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints556
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_556 (j : Fin 16) (hj : 16*556+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*556+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*556+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8896) ≤ val WuPaper.ClassicalFourthData.Bq 8896
    have hp : val WuPaper.ClassicalFourthData.Bq 8896 = (277136085383323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8896 = 277136085383323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8896 = (528:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8897) ≤ val WuPaper.ClassicalFourthData.Bq 8897
    have hp : val WuPaper.ClassicalFourthData.Bq 8897 = (277138039907005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8897 = 277138039907005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8897 = (16897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8898) ≤ val WuPaper.ClassicalFourthData.Bq 8898
    have hp : val WuPaper.ClassicalFourthData.Bq 8898 = (277139992776216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8898 = 277139992776216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8898 = (8449:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8899) ≤ val WuPaper.ClassicalFourthData.Bq 8899
    have hp : val WuPaper.ClassicalFourthData.Bq 8899 = (277141943991470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8899 = 277141943991470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8899 = (16899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8900) ≤ val WuPaper.ClassicalFourthData.Bq 8900
    have hp : val WuPaper.ClassicalFourthData.Bq 8900 = (277143893553283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8900 = 277143893553283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8900 = (169:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8901) ≤ val WuPaper.ClassicalFourthData.Bq 8901
    have hp : val WuPaper.ClassicalFourthData.Bq 8901 = (277145841462166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8901 = 277145841462166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8901 = (16901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8902) ≤ val WuPaper.ClassicalFourthData.Bq 8902
    have hp : val WuPaper.ClassicalFourthData.Bq 8902 = (277147787718636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8902 = 277147787718636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8902 = (8451:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8903) ≤ val WuPaper.ClassicalFourthData.Bq 8903
    have hp : val WuPaper.ClassicalFourthData.Bq 8903 = (277149732323205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8903 = 277149732323205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8903 = (16903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8903
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8904) ≤ val WuPaper.ClassicalFourthData.Bq 8904
    have hp : val WuPaper.ClassicalFourthData.Bq 8904 = (277151675276386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8904 = 277151675276386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8904 = (2113:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8905) ≤ val WuPaper.ClassicalFourthData.Bq 8905
    have hp : val WuPaper.ClassicalFourthData.Bq 8905 = (277153616578694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8905 = 277153616578694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8905 = (3381:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8906) ≤ val WuPaper.ClassicalFourthData.Bq 8906
    have hp : val WuPaper.ClassicalFourthData.Bq 8906 = (277155556230641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8906 = 277155556230641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8906 = (8453:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8907) ≤ val WuPaper.ClassicalFourthData.Bq 8907
    have hp : val WuPaper.ClassicalFourthData.Bq 8907 = (277157494232740:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8907 = 277157494232740 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8907 = (16907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8908) ≤ val WuPaper.ClassicalFourthData.Bq 8908
    have hp : val WuPaper.ClassicalFourthData.Bq 8908 = (277159430585504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8908 = 277159430585504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8908 = (4227:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8909) ≤ val WuPaper.ClassicalFourthData.Bq 8909
    have hp : val WuPaper.ClassicalFourthData.Bq 8909 = (277161365289446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8909 = 277161365289446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8909 = (16909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8910) ≤ val WuPaper.ClassicalFourthData.Bq 8910
    have hp : val WuPaper.ClassicalFourthData.Bq 8910 = (277163298345078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8910 = 277163298345078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8910 = (1691:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8911) ≤ val WuPaper.ClassicalFourthData.Bq 8911
    have hp : val WuPaper.ClassicalFourthData.Bq 8911 = (277165229752912:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8911 = 277165229752912 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8911 = (16911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8911
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_556
