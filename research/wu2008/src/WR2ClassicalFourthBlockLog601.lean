import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints601
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_601 (j : Fin 16) (hj : 16*601+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*601+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*601+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9616) ≤ val WuPaper.ClassicalFourthData.Bq 9616
    have hp : val WuPaper.ClassicalFourthData.Bq 9616 = (278145143224932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9616 = 278145143224932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9616 = (1101:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9617) ≤ val WuPaper.ClassicalFourthData.Bq 9617
    have hp : val WuPaper.ClassicalFourthData.Bq 9617 = (278146029647296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9617 = 278146029647296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9617 = (17617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9618) ≤ val WuPaper.ClassicalFourthData.Bq 9618
    have hp : val WuPaper.ClassicalFourthData.Bq 9618 = (278146914744586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9618 = 278146914744586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9618 = (8809:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9619) ≤ val WuPaper.ClassicalFourthData.Bq 9619
    have hp : val WuPaper.ClassicalFourthData.Bq 9619 = (278147798517205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9619 = 278147798517205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9619 = (17619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9620) ≤ val WuPaper.ClassicalFourthData.Bq 9620
    have hp : val WuPaper.ClassicalFourthData.Bq 9620 = (278148680965559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9620 = 278148680965559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9620 = (881:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9621) ≤ val WuPaper.ClassicalFourthData.Bq 9621
    have hp : val WuPaper.ClassicalFourthData.Bq 9621 = (278149562090054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9621 = 278149562090054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9621 = (17621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9622) ≤ val WuPaper.ClassicalFourthData.Bq 9622
    have hp : val WuPaper.ClassicalFourthData.Bq 9622 = (278150441891095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9622 = 278150441891095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9622 = (8811:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9623) ≤ val WuPaper.ClassicalFourthData.Bq 9623
    have hp : val WuPaper.ClassicalFourthData.Bq 9623 = (278151320369086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9623 = 278151320369086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9623 = (17623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9623
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9624) ≤ val WuPaper.ClassicalFourthData.Bq 9624
    have hp : val WuPaper.ClassicalFourthData.Bq 9624 = (278152197524433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9624 = 278152197524433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9624 = (2203:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9625) ≤ val WuPaper.ClassicalFourthData.Bq 9625
    have hp : val WuPaper.ClassicalFourthData.Bq 9625 = (278153073357539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9625 = 278153073357539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9625 = (141:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9626) ≤ val WuPaper.ClassicalFourthData.Bq 9626
    have hp : val WuPaper.ClassicalFourthData.Bq 9626 = (278153947868810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9626 = 278153947868810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9626 = (8813:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9627) ≤ val WuPaper.ClassicalFourthData.Bq 9627
    have hp : val WuPaper.ClassicalFourthData.Bq 9627 = (278154821058650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9627 = 278154821058650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9627 = (17627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9628) ≤ val WuPaper.ClassicalFourthData.Bq 9628
    have hp : val WuPaper.ClassicalFourthData.Bq 9628 = (278155692927463:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9628 = 278155692927463 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9628 = (4407:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9629) ≤ val WuPaper.ClassicalFourthData.Bq 9629
    have hp : val WuPaper.ClassicalFourthData.Bq 9629 = (278156563475653:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9629 = 278156563475653 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9629 = (17629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9630) ≤ val WuPaper.ClassicalFourthData.Bq 9630
    have hp : val WuPaper.ClassicalFourthData.Bq 9630 = (278157432703624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9630 = 278157432703624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9630 = (1763:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9631) ≤ val WuPaper.ClassicalFourthData.Bq 9631
    have hp : val WuPaper.ClassicalFourthData.Bq 9631 = (278158300611780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9631 = 278158300611780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9631 = (17631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9631
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_601
