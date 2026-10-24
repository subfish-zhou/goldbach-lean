import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints350
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_350 (j : Fin 16) (hj : 16*350+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*350+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*350+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5600) ≤ val WuPaper.ClassicalFourthData.Bq 5600
    have hp : val WuPaper.ClassicalFourthData.Bq 5600 = (257490805104090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5600 = 257490805104090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5600 = (17:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5601) ≤ val WuPaper.ClassicalFourthData.Bq 5601
    have hp : val WuPaper.ClassicalFourthData.Bq 5601 = (257502506755563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5601 = 257502506755563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5601 = (13601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5602) ≤ val WuPaper.ClassicalFourthData.Bq 5602
    have hp : val WuPaper.ClassicalFourthData.Bq 5602 = (257514203496211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5602 = 257514203496211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5602 = (6801:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5603) ≤ val WuPaper.ClassicalFourthData.Bq 5603
    have hp : val WuPaper.ClassicalFourthData.Bq 5603 = (257525895327781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5603 = 257525895327781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5603 = (13603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5604) ≤ val WuPaper.ClassicalFourthData.Bq 5604
    have hp : val WuPaper.ClassicalFourthData.Bq 5604 = (257537582252021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5604 = 257537582252021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5604 = (3401:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5605) ≤ val WuPaper.ClassicalFourthData.Bq 5605
    have hp : val WuPaper.ClassicalFourthData.Bq 5605 = (257549264270676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5605 = 257549264270676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5605 = (2721:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5606) ≤ val WuPaper.ClassicalFourthData.Bq 5606
    have hp : val WuPaper.ClassicalFourthData.Bq 5606 = (257560941385491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5606 = 257560941385491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5606 = (6803:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5607) ≤ val WuPaper.ClassicalFourthData.Bq 5607
    have hp : val WuPaper.ClassicalFourthData.Bq 5607 = (257572613598212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5607 = 257572613598212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5607 = (13607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5607
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5608) ≤ val WuPaper.ClassicalFourthData.Bq 5608
    have hp : val WuPaper.ClassicalFourthData.Bq 5608 = (257584280910581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5608 = 257584280910581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5608 = (1701:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5609) ≤ val WuPaper.ClassicalFourthData.Bq 5609
    have hp : val WuPaper.ClassicalFourthData.Bq 5609 = (257595943324343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5609 = 257595943324343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5609 = (13609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5610) ≤ val WuPaper.ClassicalFourthData.Bq 5610
    have hp : val WuPaper.ClassicalFourthData.Bq 5610 = (257607600841239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5610 = 257607600841239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5610 = (1361:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5611) ≤ val WuPaper.ClassicalFourthData.Bq 5611
    have hp : val WuPaper.ClassicalFourthData.Bq 5611 = (257619253463012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5611 = 257619253463012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5611 = (13611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5612) ≤ val WuPaper.ClassicalFourthData.Bq 5612
    have hp : val WuPaper.ClassicalFourthData.Bq 5612 = (257630901191401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5612 = 257630901191401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5612 = (3403:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5613) ≤ val WuPaper.ClassicalFourthData.Bq 5613
    have hp : val WuPaper.ClassicalFourthData.Bq 5613 = (257642544028148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5613 = 257642544028148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5613 = (13613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5614) ≤ val WuPaper.ClassicalFourthData.Bq 5614
    have hp : val WuPaper.ClassicalFourthData.Bq 5614 = (257654181974992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5614 = 257654181974992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5614 = (6807:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5615) ≤ val WuPaper.ClassicalFourthData.Bq 5615
    have hp : val WuPaper.ClassicalFourthData.Bq 5615 = (257665815033671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5615 = 257665815033671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5615 = (2723:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_350
