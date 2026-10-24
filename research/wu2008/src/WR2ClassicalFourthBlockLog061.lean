import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints061
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_061 (j : Fin 16) (hj : 16*61+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*61+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*61+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 976) ≤ val WuPaper.ClassicalFourthData.Bq 976
    have hp : val WuPaper.ClassicalFourthData.Bq 976 = (97295897645717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 976 = 97295897645717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 976 = (561:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 977) ≤ val WuPaper.ClassicalFourthData.Bq 977
    have hp : val WuPaper.ClassicalFourthData.Bq 977 = (97374596750152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 977 = 97374596750152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 977 = (8977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 978) ≤ val WuPaper.ClassicalFourthData.Bq 978
    have hp : val WuPaper.ClassicalFourthData.Bq 978 = (97453260336605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 978 = 97453260336605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 978 = (4489:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 979) ≤ val WuPaper.ClassicalFourthData.Bq 979
    have hp : val WuPaper.ClassicalFourthData.Bq 979 = (97531888424170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 979 = 97531888424170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 979 = (8979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 980) ≤ val WuPaper.ClassicalFourthData.Bq 980
    have hp : val WuPaper.ClassicalFourthData.Bq 980 = (97610481031925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 980 = 97610481031925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 980 = (449:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 981) ≤ val WuPaper.ClassicalFourthData.Bq 981
    have hp : val WuPaper.ClassicalFourthData.Bq 981 = (97689038178936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 981 = 97689038178936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 981 = (8981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 982) ≤ val WuPaper.ClassicalFourthData.Bq 982
    have hp : val WuPaper.ClassicalFourthData.Bq 982 = (97767559884257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 982 = 97767559884257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 982 = (4491:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 983) ≤ val WuPaper.ClassicalFourthData.Bq 983
    have hp : val WuPaper.ClassicalFourthData.Bq 983 = (97846046166928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 983 = 97846046166928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 983 = (8983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_983
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 984) ≤ val WuPaper.ClassicalFourthData.Bq 984
    have hp : val WuPaper.ClassicalFourthData.Bq 984 = (97924497045976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 984 = 97924497045976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 984 = (1123:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 985) ≤ val WuPaper.ClassicalFourthData.Bq 985
    have hp : val WuPaper.ClassicalFourthData.Bq 985 = (98002912540417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 985 = 98002912540417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 985 = (1797:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 986) ≤ val WuPaper.ClassicalFourthData.Bq 986
    have hp : val WuPaper.ClassicalFourthData.Bq 986 = (98081292669253:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 986 = 98081292669253 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 986 = (4493:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 987) ≤ val WuPaper.ClassicalFourthData.Bq 987
    have hp : val WuPaper.ClassicalFourthData.Bq 987 = (98159637451473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 987 = 98159637451473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 987 = (8987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 988) ≤ val WuPaper.ClassicalFourthData.Bq 988
    have hp : val WuPaper.ClassicalFourthData.Bq 988 = (98237946906053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 988 = 98237946906053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 988 = (2247:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 989) ≤ val WuPaper.ClassicalFourthData.Bq 989
    have hp : val WuPaper.ClassicalFourthData.Bq 989 = (98316221051957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 989 = 98316221051957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 989 = (8989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 990) ≤ val WuPaper.ClassicalFourthData.Bq 990
    have hp : val WuPaper.ClassicalFourthData.Bq 990 = (98394459908137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 990 = 98394459908137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 990 = (899:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 991) ≤ val WuPaper.ClassicalFourthData.Bq 991
    have hp : val WuPaper.ClassicalFourthData.Bq 991 = (98472663493530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 991 = 98472663493530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 991 = (8991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_991
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_061
