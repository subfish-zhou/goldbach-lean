import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints440
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_440 (j : Fin 16) (hj : 16*440+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*440+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*440+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7040) ≤ val WuPaper.ClassicalFourthData.Bq 7040
    have hp : val WuPaper.ClassicalFourthData.Bq 7040 = (270008159502485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7040 = 270008159502485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7040 = (94:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7041) ≤ val WuPaper.ClassicalFourthData.Bq 7041
    have hp : val WuPaper.ClassicalFourthData.Bq 7041 = (270014295681775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7041 = 270014295681775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7041 = (15041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7042) ≤ val WuPaper.ClassicalFourthData.Bq 7042
    have hp : val WuPaper.ClassicalFourthData.Bq 7042 = (270020428863781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7042 = 270020428863781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7042 = (7521:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7043) ≤ val WuPaper.ClassicalFourthData.Bq 7043
    have hp : val WuPaper.ClassicalFourthData.Bq 7043 = (270026559049496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7043 = 270026559049496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7043 = (15043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7044) ≤ val WuPaper.ClassicalFourthData.Bq 7044
    have hp : val WuPaper.ClassicalFourthData.Bq 7044 = (270032686239911:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7044 = 270032686239911 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7044 = (3761:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7045) ≤ val WuPaper.ClassicalFourthData.Bq 7045
    have hp : val WuPaper.ClassicalFourthData.Bq 7045 = (270038810436020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7045 = 270038810436020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7045 = (3009:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7046) ≤ val WuPaper.ClassicalFourthData.Bq 7046
    have hp : val WuPaper.ClassicalFourthData.Bq 7046 = (270044931638813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7046 = 270044931638813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7046 = (7523:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7047) ≤ val WuPaper.ClassicalFourthData.Bq 7047
    have hp : val WuPaper.ClassicalFourthData.Bq 7047 = (270051049849282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7047 = 270051049849282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7047 = (15047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7047
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7048) ≤ val WuPaper.ClassicalFourthData.Bq 7048
    have hp : val WuPaper.ClassicalFourthData.Bq 7048 = (270057165068419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7048 = 270057165068419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7048 = (1881:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7049) ≤ val WuPaper.ClassicalFourthData.Bq 7049
    have hp : val WuPaper.ClassicalFourthData.Bq 7049 = (270063277297213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7049 = 270063277297213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7049 = (15049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7050) ≤ val WuPaper.ClassicalFourthData.Bq 7050
    have hp : val WuPaper.ClassicalFourthData.Bq 7050 = (270069386536655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7050 = 270069386536655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7050 = (301:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7051) ≤ val WuPaper.ClassicalFourthData.Bq 7051
    have hp : val WuPaper.ClassicalFourthData.Bq 7051 = (270075492787735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7051 = 270075492787735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7051 = (15051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7052) ≤ val WuPaper.ClassicalFourthData.Bq 7052
    have hp : val WuPaper.ClassicalFourthData.Bq 7052 = (270081596051441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7052 = 270081596051441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7052 = (3763:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7053) ≤ val WuPaper.ClassicalFourthData.Bq 7053
    have hp : val WuPaper.ClassicalFourthData.Bq 7053 = (270087696328764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7053 = 270087696328764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7053 = (15053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7054) ≤ val WuPaper.ClassicalFourthData.Bq 7054
    have hp : val WuPaper.ClassicalFourthData.Bq 7054 = (270093793620693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7054 = 270093793620693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7054 = (7527:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7055) ≤ val WuPaper.ClassicalFourthData.Bq 7055
    have hp : val WuPaper.ClassicalFourthData.Bq 7055 = (270099887928214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7055 = 270099887928214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7055 = (3011:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_440
