import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints224
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_224 (j : Fin 16) (hj : 16*224+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*224+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*224+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3584) ≤ val WuPaper.ClassicalFourthData.Bq 3584
    have hp : val WuPaper.ClassicalFourthData.Bq 3584 = (220906907400840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3584 = 220906907400840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3584 = (362:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3585) ≤ val WuPaper.ClassicalFourthData.Bq 3585
    have hp : val WuPaper.ClassicalFourthData.Bq 3585 = (220933362686442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3585 = 220933362686442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3585 = (2317:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3586) ≤ val WuPaper.ClassicalFourthData.Bq 3586
    have hp : val WuPaper.ClassicalFourthData.Bq 3586 = (220959807404391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3586 = 220959807404391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3586 = (5793:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3587) ≤ val WuPaper.ClassicalFourthData.Bq 3587
    have hp : val WuPaper.ClassicalFourthData.Bq 3587 = (220986241559005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3587 = 220986241559005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3587 = (11587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3588) ≤ val WuPaper.ClassicalFourthData.Bq 3588
    have hp : val WuPaper.ClassicalFourthData.Bq 3588 = (221012665154601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3588 = 221012665154601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3588 = (2897:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3589) ≤ val WuPaper.ClassicalFourthData.Bq 3589
    have hp : val WuPaper.ClassicalFourthData.Bq 3589 = (221039078195491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3589 = 221039078195491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3589 = (11589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3590) ≤ val WuPaper.ClassicalFourthData.Bq 3590
    have hp : val WuPaper.ClassicalFourthData.Bq 3590 = (221065480685988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3590 = 221065480685988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3590 = (1159:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3591) ≤ val WuPaper.ClassicalFourthData.Bq 3591
    have hp : val WuPaper.ClassicalFourthData.Bq 3591 = (221091872630400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3591 = 221091872630400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3591 = (11591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3591
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3592) ≤ val WuPaper.ClassicalFourthData.Bq 3592
    have hp : val WuPaper.ClassicalFourthData.Bq 3592 = (221118254033036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3592 = 221118254033036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3592 = (1449:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3593) ≤ val WuPaper.ClassicalFourthData.Bq 3593
    have hp : val WuPaper.ClassicalFourthData.Bq 3593 = (221144624898200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3593 = 221144624898200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3593 = (11593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3594) ≤ val WuPaper.ClassicalFourthData.Bq 3594
    have hp : val WuPaper.ClassicalFourthData.Bq 3594 = (221170985230195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3594 = 221170985230195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3594 = (5797:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3595) ≤ val WuPaper.ClassicalFourthData.Bq 3595
    have hp : val WuPaper.ClassicalFourthData.Bq 3595 = (221197335033324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3595 = 221197335033324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3595 = (2319:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3596) ≤ val WuPaper.ClassicalFourthData.Bq 3596
    have hp : val WuPaper.ClassicalFourthData.Bq 3596 = (221223674311884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3596 = 221223674311884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3596 = (2899:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3597) ≤ val WuPaper.ClassicalFourthData.Bq 3597
    have hp : val WuPaper.ClassicalFourthData.Bq 3597 = (221250003070172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3597 = 221250003070172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3597 = (11597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3598) ≤ val WuPaper.ClassicalFourthData.Bq 3598
    have hp : val WuPaper.ClassicalFourthData.Bq 3598 = (221276321312483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3598 = 221276321312483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3598 = (5799:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3599) ≤ val WuPaper.ClassicalFourthData.Bq 3599
    have hp : val WuPaper.ClassicalFourthData.Bq 3599 = (221302629043110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3599 = 221302629043110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3599 = (11599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3599
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_224
