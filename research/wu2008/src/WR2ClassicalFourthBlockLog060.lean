import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints060
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_060 (j : Fin 16) (hj : 16*60+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*60+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*60+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 960) ≤ val WuPaper.ClassicalFourthData.Bq 960
    have hp : val WuPaper.ClassicalFourthData.Bq 960 = (96031865900423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 960 = 96031865900423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 960 = (56:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 961) ≤ val WuPaper.ClassicalFourthData.Bq 961
    have hp : val WuPaper.ClassicalFourthData.Bq 961 = (96111135899575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 961 = 96111135899575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 961 = (8961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 962) ≤ val WuPaper.ClassicalFourthData.Bq 962
    have hp : val WuPaper.ClassicalFourthData.Bq 962 = (96190370073519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 962 = 96190370073519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 962 = (4481:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 963) ≤ val WuPaper.ClassicalFourthData.Bq 963
    have hp : val WuPaper.ClassicalFourthData.Bq 963 = (96269568441555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 963 = 96269568441555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 963 = (8963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 964) ≤ val WuPaper.ClassicalFourthData.Bq 964
    have hp : val WuPaper.ClassicalFourthData.Bq 964 = (96348731022968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 964 = 96348731022968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 964 = (2241:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 965) ≤ val WuPaper.ClassicalFourthData.Bq 965
    have hp : val WuPaper.ClassicalFourthData.Bq 965 = (96427857837031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 965 = 96427857837031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 965 = (1793:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 966) ≤ val WuPaper.ClassicalFourthData.Bq 966
    have hp : val WuPaper.ClassicalFourthData.Bq 966 = (96506948903005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 966 = 96506948903005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 966 = (4483:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 967) ≤ val WuPaper.ClassicalFourthData.Bq 967
    have hp : val WuPaper.ClassicalFourthData.Bq 967 = (96586004240136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 967 = 96586004240136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 967 = (8967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_967
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 968) ≤ val WuPaper.ClassicalFourthData.Bq 968
    have hp : val WuPaper.ClassicalFourthData.Bq 968 = (96665023867658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 968 = 96665023867658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 968 = (1121:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 969) ≤ val WuPaper.ClassicalFourthData.Bq 969
    have hp : val WuPaper.ClassicalFourthData.Bq 969 = (96744007804792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 969 = 96744007804792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 969 = (8969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 970) ≤ val WuPaper.ClassicalFourthData.Bq 970
    have hp : val WuPaper.ClassicalFourthData.Bq 970 = (96822956070746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 970 = 96822956070746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 970 = (897:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 971) ≤ val WuPaper.ClassicalFourthData.Bq 971
    have hp : val WuPaper.ClassicalFourthData.Bq 971 = (96901868684716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 971 = 96901868684716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 971 = (8971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 972) ≤ val WuPaper.ClassicalFourthData.Bq 972
    have hp : val WuPaper.ClassicalFourthData.Bq 972 = (96980745665883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 972 = 96980745665883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 972 = (2243:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 973) ≤ val WuPaper.ClassicalFourthData.Bq 973
    have hp : val WuPaper.ClassicalFourthData.Bq 973 = (97059587033417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 973 = 97059587033417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 973 = (8973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 974) ≤ val WuPaper.ClassicalFourthData.Bq 974
    have hp : val WuPaper.ClassicalFourthData.Bq 974 = (97138392806474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 974 = 97138392806474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 974 = (4487:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 975) ≤ val WuPaper.ClassicalFourthData.Bq 975
    have hp : val WuPaper.ClassicalFourthData.Bq 975 = (97217163004197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 975 = 97217163004197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 975 = (359:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_060
