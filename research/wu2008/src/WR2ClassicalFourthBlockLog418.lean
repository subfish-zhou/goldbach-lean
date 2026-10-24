import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints418
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_418 (j : Fin 16) (hj : 16*418+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*418+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*418+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6688) ≤ val WuPaper.ClassicalFourthData.Bq 6688
    have hp : val WuPaper.ClassicalFourthData.Bq 6688 = (267654481392842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6688 = 267654481392842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6688 = (459:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6689) ≤ val WuPaper.ClassicalFourthData.Bq 6689
    have hp : val WuPaper.ClassicalFourthData.Bq 6689 = (267661737129018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6689 = 267661737129018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6689 = (14689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6690) ≤ val WuPaper.ClassicalFourthData.Bq 6690
    have hp : val WuPaper.ClassicalFourthData.Bq 6690 = (267668989494127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6690 = 267668989494127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6690 = (1469:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6691) ≤ val WuPaper.ClassicalFourthData.Bq 6691
    have hp : val WuPaper.ClassicalFourthData.Bq 6691 = (267676238489304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6691 = 267676238489304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6691 = (14691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6692) ≤ val WuPaper.ClassicalFourthData.Bq 6692
    have hp : val WuPaper.ClassicalFourthData.Bq 6692 = (267683484115682:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6692 = 267683484115682 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6692 = (3673:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6693) ≤ val WuPaper.ClassicalFourthData.Bq 6693
    have hp : val WuPaper.ClassicalFourthData.Bq 6693 = (267690726374395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6693 = 267690726374395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6693 = (14693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6694) ≤ val WuPaper.ClassicalFourthData.Bq 6694
    have hp : val WuPaper.ClassicalFourthData.Bq 6694 = (267697965266576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6694 = 267697965266576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6694 = (7347:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6695) ≤ val WuPaper.ClassicalFourthData.Bq 6695
    have hp : val WuPaper.ClassicalFourthData.Bq 6695 = (267705200793358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6695 = 267705200793358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6695 = (2939:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6695
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6696) ≤ val WuPaper.ClassicalFourthData.Bq 6696
    have hp : val WuPaper.ClassicalFourthData.Bq 6696 = (267712432955871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6696 = 267712432955871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6696 = (1837:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6697) ≤ val WuPaper.ClassicalFourthData.Bq 6697
    have hp : val WuPaper.ClassicalFourthData.Bq 6697 = (267719661755249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6697 = 267719661755249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6697 = (14697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6698) ≤ val WuPaper.ClassicalFourthData.Bq 6698
    have hp : val WuPaper.ClassicalFourthData.Bq 6698 = (267726887192621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6698 = 267726887192621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6698 = (7349:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6699) ≤ val WuPaper.ClassicalFourthData.Bq 6699
    have hp : val WuPaper.ClassicalFourthData.Bq 6699 = (267734109269120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6699 = 267734109269120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6699 = (14699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6700) ≤ val WuPaper.ClassicalFourthData.Bq 6700
    have hp : val WuPaper.ClassicalFourthData.Bq 6700 = (267741327985875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6700 = 267741327985875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6700 = (147:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6701) ≤ val WuPaper.ClassicalFourthData.Bq 6701
    have hp : val WuPaper.ClassicalFourthData.Bq 6701 = (267748543344016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6701 = 267748543344016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6701 = (14701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6702) ≤ val WuPaper.ClassicalFourthData.Bq 6702
    have hp : val WuPaper.ClassicalFourthData.Bq 6702 = (267755755344672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6702 = 267755755344672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6702 = (7351:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6703) ≤ val WuPaper.ClassicalFourthData.Bq 6703
    have hp : val WuPaper.ClassicalFourthData.Bq 6703 = (267762963988974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6703 = 267762963988974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6703 = (14703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_418
