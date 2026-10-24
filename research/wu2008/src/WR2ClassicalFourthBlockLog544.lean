import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints544
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_544 (j : Fin 16) (hj : 16*544+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*544+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*544+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8704) ≤ val WuPaper.ClassicalFourthData.Bq 8704
    have hp : val WuPaper.ClassicalFourthData.Bq 8704 = (276729536253649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8704 = 276729536253649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8704 = (522:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8705) ≤ val WuPaper.ClassicalFourthData.Bq 8705
    have hp : val WuPaper.ClassicalFourthData.Bq 8705 = (276731818177218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8705 = 276731818177218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8705 = (3341:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8706) ≤ val WuPaper.ClassicalFourthData.Bq 8706
    have hp : val WuPaper.ClassicalFourthData.Bq 8706 = (276734098344269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8706 = 276734098344269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8706 = (8353:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8707) ≤ val WuPaper.ClassicalFourthData.Bq 8707
    have hp : val WuPaper.ClassicalFourthData.Bq 8707 = (276736376755352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8707 = 276736376755352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8707 = (16707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8708) ≤ val WuPaper.ClassicalFourthData.Bq 8708
    have hp : val WuPaper.ClassicalFourthData.Bq 8708 = (276738653411014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8708 = 276738653411014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8708 = (4177:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8709) ≤ val WuPaper.ClassicalFourthData.Bq 8709
    have hp : val WuPaper.ClassicalFourthData.Bq 8709 = (276740928311806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8709 = 276740928311806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8709 = (16709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8710) ≤ val WuPaper.ClassicalFourthData.Bq 8710
    have hp : val WuPaper.ClassicalFourthData.Bq 8710 = (276743201458274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8710 = 276743201458274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8710 = (1671:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8711) ≤ val WuPaper.ClassicalFourthData.Bq 8711
    have hp : val WuPaper.ClassicalFourthData.Bq 8711 = (276745472850967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8711 = 276745472850967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8711 = (16711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8711
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8712) ≤ val WuPaper.ClassicalFourthData.Bq 8712
    have hp : val WuPaper.ClassicalFourthData.Bq 8712 = (276747742490433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8712 = 276747742490433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8712 = (2089:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8713) ≤ val WuPaper.ClassicalFourthData.Bq 8713
    have hp : val WuPaper.ClassicalFourthData.Bq 8713 = (276750010377220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8713 = 276750010377220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8713 = (16713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8714) ≤ val WuPaper.ClassicalFourthData.Bq 8714
    have hp : val WuPaper.ClassicalFourthData.Bq 8714 = (276752276511876:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8714 = 276752276511876 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8714 = (8357:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8715) ≤ val WuPaper.ClassicalFourthData.Bq 8715
    have hp : val WuPaper.ClassicalFourthData.Bq 8715 = (276754540894947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8715 = 276754540894947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8715 = (3343:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8716) ≤ val WuPaper.ClassicalFourthData.Bq 8716
    have hp : val WuPaper.ClassicalFourthData.Bq 8716 = (276756803526980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8716 = 276756803526980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8716 = (4179:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8717) ≤ val WuPaper.ClassicalFourthData.Bq 8717
    have hp : val WuPaper.ClassicalFourthData.Bq 8717 = (276759064408524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8717 = 276759064408524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8717 = (16717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8718) ≤ val WuPaper.ClassicalFourthData.Bq 8718
    have hp : val WuPaper.ClassicalFourthData.Bq 8718 = (276761323540125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8718 = 276761323540125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8718 = (8359:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8719) ≤ val WuPaper.ClassicalFourthData.Bq 8719
    have hp : val WuPaper.ClassicalFourthData.Bq 8719 = (276763580922328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8719 = 276763580922328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8719 = (16719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_544
