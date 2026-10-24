import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints416
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_416 (j : Fin 16) (hj : 16*416+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*416+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*416+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6656) ≤ val WuPaper.ClassicalFourthData.Bq 6656
    have hp : val WuPaper.ClassicalFourthData.Bq 6656 = (267420511102142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6656 = 267420511102142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6656 = (458:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6657) ≤ val WuPaper.ClassicalFourthData.Bq 6657
    have hp : val WuPaper.ClassicalFourthData.Bq 6657 = (267427875313921:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6657 = 267427875313921 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6657 = (14657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6658) ≤ val WuPaper.ClassicalFourthData.Bq 6658
    have hp : val WuPaper.ClassicalFourthData.Bq 6658 = (267435236118108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6658 = 267435236118108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6658 = (7329:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6659) ≤ val WuPaper.ClassicalFourthData.Bq 6659
    have hp : val WuPaper.ClassicalFourthData.Bq 6659 = (267442593515852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6659 = 267442593515852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6659 = (14659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6660) ≤ val WuPaper.ClassicalFourthData.Bq 6660
    have hp : val WuPaper.ClassicalFourthData.Bq 6660 = (267449947508299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6660 = 267449947508299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6660 = (733:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6661) ≤ val WuPaper.ClassicalFourthData.Bq 6661
    have hp : val WuPaper.ClassicalFourthData.Bq 6661 = (267457298096598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6661 = 267457298096598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6661 = (14661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6662) ≤ val WuPaper.ClassicalFourthData.Bq 6662
    have hp : val WuPaper.ClassicalFourthData.Bq 6662 = (267464645281895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6662 = 267464645281895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6662 = (7331:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6663) ≤ val WuPaper.ClassicalFourthData.Bq 6663
    have hp : val WuPaper.ClassicalFourthData.Bq 6663 = (267471989065338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6663 = 267471989065338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6663 = (14663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6663
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6664) ≤ val WuPaper.ClassicalFourthData.Bq 6664
    have hp : val WuPaper.ClassicalFourthData.Bq 6664 = (267479329448071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6664 = 267479329448071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6664 = (1833:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6665) ≤ val WuPaper.ClassicalFourthData.Bq 6665
    have hp : val WuPaper.ClassicalFourthData.Bq 6665 = (267486666431240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6665 = 267486666431240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6665 = (2933:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6666) ≤ val WuPaper.ClassicalFourthData.Bq 6666
    have hp : val WuPaper.ClassicalFourthData.Bq 6666 = (267494000015991:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6666 = 267494000015991 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6666 = (7333:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6667) ≤ val WuPaper.ClassicalFourthData.Bq 6667
    have hp : val WuPaper.ClassicalFourthData.Bq 6667 = (267501330203468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6667 = 267501330203468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6667 = (14667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6668) ≤ val WuPaper.ClassicalFourthData.Bq 6668
    have hp : val WuPaper.ClassicalFourthData.Bq 6668 = (267508656994815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6668 = 267508656994815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6668 = (3667:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6669) ≤ val WuPaper.ClassicalFourthData.Bq 6669
    have hp : val WuPaper.ClassicalFourthData.Bq 6669 = (267515980391177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6669 = 267515980391177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6669 = (14669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6670) ≤ val WuPaper.ClassicalFourthData.Bq 6670
    have hp : val WuPaper.ClassicalFourthData.Bq 6670 = (267523300393697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6670 = 267523300393697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6670 = (1467:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6671) ≤ val WuPaper.ClassicalFourthData.Bq 6671
    have hp : val WuPaper.ClassicalFourthData.Bq 6671 = (267530617003517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6671 = 267530617003517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6671 = (14671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_416
