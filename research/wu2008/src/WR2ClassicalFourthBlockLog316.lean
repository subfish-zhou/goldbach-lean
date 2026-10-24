import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints316
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_316 (j : Fin 16) (hj : 16*316+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*316+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*316+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5056) ≤ val WuPaper.ClassicalFourthData.Bq 5056
    have hp : val WuPaper.ClassicalFourthData.Bq 5056 = (250347169222101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5056 = 250347169222101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5056 = (408:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5057) ≤ val WuPaper.ClassicalFourthData.Bq 5057
    have hp : val WuPaper.ClassicalFourthData.Bq 5057 = (250361822247966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5057 = 250361822247966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5057 = (13057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5058) ≤ val WuPaper.ClassicalFourthData.Bq 5058
    have hp : val WuPaper.ClassicalFourthData.Bq 5058 = (250376469295186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5058 = 250376469295186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5058 = (6529:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5059) ≤ val WuPaper.ClassicalFourthData.Bq 5059
    have hp : val WuPaper.ClassicalFourthData.Bq 5059 = (250391110365958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5059 = 250391110365958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5059 = (13059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5060) ≤ val WuPaper.ClassicalFourthData.Bq 5060
    have hp : val WuPaper.ClassicalFourthData.Bq 5060 = (250405745462481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5060 = 250405745462481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5060 = (653:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5061) ≤ val WuPaper.ClassicalFourthData.Bq 5061
    have hp : val WuPaper.ClassicalFourthData.Bq 5061 = (250420374586949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5061 = 250420374586949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5061 = (13061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5062) ≤ val WuPaper.ClassicalFourthData.Bq 5062
    have hp : val WuPaper.ClassicalFourthData.Bq 5062 = (250434997741558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5062 = 250434997741558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5062 = (6531:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5063) ≤ val WuPaper.ClassicalFourthData.Bq 5063
    have hp : val WuPaper.ClassicalFourthData.Bq 5063 = (250449614928502:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5063 = 250449614928502 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5063 = (13063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5063
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5064) ≤ val WuPaper.ClassicalFourthData.Bq 5064
    have hp : val WuPaper.ClassicalFourthData.Bq 5064 = (250464226149975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5064 = 250464226149975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5064 = (1633:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5065) ≤ val WuPaper.ClassicalFourthData.Bq 5065
    have hp : val WuPaper.ClassicalFourthData.Bq 5065 = (250478831408167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5065 = 250478831408167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5065 = (2613:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5066) ≤ val WuPaper.ClassicalFourthData.Bq 5066
    have hp : val WuPaper.ClassicalFourthData.Bq 5066 = (250493430705271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5066 = 250493430705271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5066 = (6533:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5067) ≤ val WuPaper.ClassicalFourthData.Bq 5067
    have hp : val WuPaper.ClassicalFourthData.Bq 5067 = (250508024043478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5067 = 250508024043478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5067 = (13067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5068) ≤ val WuPaper.ClassicalFourthData.Bq 5068
    have hp : val WuPaper.ClassicalFourthData.Bq 5068 = (250522611424975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5068 = 250522611424975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5068 = (3267:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5069) ≤ val WuPaper.ClassicalFourthData.Bq 5069
    have hp : val WuPaper.ClassicalFourthData.Bq 5069 = (250537192851953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5069 = 250537192851953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5069 = (13069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5070) ≤ val WuPaper.ClassicalFourthData.Bq 5070
    have hp : val WuPaper.ClassicalFourthData.Bq 5070 = (250551768326597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5070 = 250551768326597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5070 = (1307:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5071) ≤ val WuPaper.ClassicalFourthData.Bq 5071
    have hp : val WuPaper.ClassicalFourthData.Bq 5071 = (250566337851096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5071 = 250566337851096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5071 = (13071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_316
