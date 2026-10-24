import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints227
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_227 (j : Fin 16) (hj : 16*227+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*227+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*227+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3632) ≤ val WuPaper.ClassicalFourthData.Bq 3632
    have hp : val WuPaper.ClassicalFourthData.Bq 3632 = (222164915070872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3632 = 222164915070872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3632 = (727:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3633) ≤ val WuPaper.ClassicalFourthData.Bq 3633
    have hp : val WuPaper.ClassicalFourthData.Bq 3633 = (222190867943418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3633 = 222190867943418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3633 = (11633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3634) ≤ val WuPaper.ClassicalFourthData.Bq 3634
    have hp : val WuPaper.ClassicalFourthData.Bq 3634 = (222216810453206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3634 = 222216810453206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3634 = (5817:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3635) ≤ val WuPaper.ClassicalFourthData.Bq 3635
    have hp : val WuPaper.ClassicalFourthData.Bq 3635 = (222242742604454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3635 = 222242742604454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3635 = (2327:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3636) ≤ val WuPaper.ClassicalFourthData.Bq 3636
    have hp : val WuPaper.ClassicalFourthData.Bq 3636 = (222268664401379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3636 = 222268664401379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3636 = (2909:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3637) ≤ val WuPaper.ClassicalFourthData.Bq 3637
    have hp : val WuPaper.ClassicalFourthData.Bq 3637 = (222294575848194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3637 = 222294575848194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3637 = (11637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3638) ≤ val WuPaper.ClassicalFourthData.Bq 3638
    have hp : val WuPaper.ClassicalFourthData.Bq 3638 = (222320476949110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3638 = 222320476949110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3638 = (5819:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3639) ≤ val WuPaper.ClassicalFourthData.Bq 3639
    have hp : val WuPaper.ClassicalFourthData.Bq 3639 = (222346367708337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3639 = 222346367708337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3639 = (11639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3639
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3640) ≤ val WuPaper.ClassicalFourthData.Bq 3640
    have hp : val WuPaper.ClassicalFourthData.Bq 3640 = (222372248130082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3640 = 222372248130082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3640 = (291:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3641) ≤ val WuPaper.ClassicalFourthData.Bq 3641
    have hp : val WuPaper.ClassicalFourthData.Bq 3641 = (222398118218552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3641 = 222398118218552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3641 = (11641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3642) ≤ val WuPaper.ClassicalFourthData.Bq 3642
    have hp : val WuPaper.ClassicalFourthData.Bq 3642 = (222423977977948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3642 = 222423977977948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3642 = (5821:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3643) ≤ val WuPaper.ClassicalFourthData.Bq 3643
    have hp : val WuPaper.ClassicalFourthData.Bq 3643 = (222449827412474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3643 = 222449827412474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3643 = (11643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3644) ≤ val WuPaper.ClassicalFourthData.Bq 3644
    have hp : val WuPaper.ClassicalFourthData.Bq 3644 = (222475666526327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3644 = 222475666526327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3644 = (2911:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3645) ≤ val WuPaper.ClassicalFourthData.Bq 3645
    have hp : val WuPaper.ClassicalFourthData.Bq 3645 = (222501495323705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3645 = 222501495323705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3645 = (2329:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3646) ≤ val WuPaper.ClassicalFourthData.Bq 3646
    have hp : val WuPaper.ClassicalFourthData.Bq 3646 = (222527313808804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3646 = 222527313808804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3646 = (5823:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3647) ≤ val WuPaper.ClassicalFourthData.Bq 3647
    have hp : val WuPaper.ClassicalFourthData.Bq 3647 = (222553121985816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3647 = 222553121985816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3647 = (11647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_227
